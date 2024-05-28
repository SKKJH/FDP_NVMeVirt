// SPDX-License-Identifier: GPL-2.0-only

#include <linux/ktime.h>
#include <linux/sched/clock.h>

#include "nvmev.h"
#include "conv_ftl.h"

static inline bool last_pg_in_wordline(struct conv_ftl *conv_ftl, struct ppa *ppa)
{
	struct ssdparams *spp = &conv_ftl->ssd->sp;
	return (ppa->g.pg % spp->pgs_per_oneshotpg) == (spp->pgs_per_oneshotpg - 1);
}

static inline bool should_fdp_gc(struct conv_ftl *conv_ftl, uint16_t rg)  //update~
{
        return (conv_ftl->ssd->rums[rg].free_ru_cnt <= conv_ftl->cp.gc_thres_rus);
}

static bool should_gc(struct conv_ftl *conv_ftl)
{
	return (conv_ftl->lm.free_line_cnt <= conv_ftl->cp.gc_thres_lines);
}

static inline bool should_fdp_gc_high(struct conv_ftl *conv_ftl, uint16_t rg)
{
	return (conv_ftl->ssd->rums[rg].free_ru_cnt <= conv_ftl->cp.gc_thres_rus_high);
}

static inline bool should_gc_high(struct conv_ftl *conv_ftl)
{
	return conv_ftl->lm.free_line_cnt <= conv_ftl->cp.gc_thres_lines_high;
}

static inline struct ppa get_maptbl_ent(struct conv_ftl *conv_ftl, uint64_t lpn)
{
	return conv_ftl->maptbl[lpn];
}

static inline void set_maptbl_ent(struct conv_ftl *conv_ftl, uint64_t lpn, struct ppa *ppa)
{
	NVMEV_ASSERT(lpn < conv_ftl->ssd->sp.tt_pgs);
	conv_ftl->maptbl[lpn] = *ppa;
}

static uint64_t ppa2pgidx(struct conv_ftl *conv_ftl, struct ppa *ppa)
{
	struct ssdparams *spp = &conv_ftl->ssd->sp;
	uint64_t pgidx;

	NVMEV_DEBUG_VERBOSE("%s: ch:%d, lun:%d, pl:%d, blk:%d, pg:%d\n", __func__,
			ppa->g.ch, ppa->g.lun, ppa->g.pl, ppa->g.blk, ppa->g.pg);

	pgidx = ppa->g.ch * spp->pgs_per_ch + ppa->g.lun * spp->pgs_per_lun +
		ppa->g.pl * spp->pgs_per_pl + ppa->g.blk * spp->pgs_per_blk + ppa->g.pg;

	NVMEV_ASSERT(pgidx < spp->tt_pgs);

	return pgidx;
}

static inline uint64_t get_rmap_ent(struct conv_ftl *conv_ftl, struct ppa *ppa)
{
	uint64_t pgidx = ppa2pgidx(conv_ftl, ppa);

	return conv_ftl->rmap[pgidx];
}

/* set rmap[page_no(ppa)] -> lpn */
static inline void set_rmap_ent(struct conv_ftl *conv_ftl, uint64_t lpn, struct ppa *ppa)
{
	uint64_t pgidx = ppa2pgidx(conv_ftl, ppa);

	conv_ftl->rmap[pgidx] = lpn;
}

static inline int victim_line_cmp_pri(pqueue_pri_t next, pqueue_pri_t curr)
{
	return (next > curr);
}

static inline pqueue_pri_t victim_line_get_pri(void *a)
{
	return ((struct line *)a)->vpc;
}

static inline void victim_line_set_pri(void *a, pqueue_pri_t pri)
{
	((struct line *)a)->vpc = pri;
}

static inline size_t victim_line_get_pos(void *a)
{
	return ((struct line *)a)->pos;
}

static inline void victim_line_set_pos(void *a, size_t pos)
{
	((struct line *)a)->pos = pos;
}

static inline void consume_write_credit(struct conv_ftl *conv_ftl)
{
	conv_ftl->wfc.write_credits--;
}

static void foreground_gc(struct conv_ftl *conv_ftl);

static inline void check_and_refill_write_credit(struct conv_ftl *conv_ftl)
{
	struct write_flow_control *wfc = &(conv_ftl->wfc);
	if (wfc->write_credits <= 0) {
		foreground_gc(conv_ftl);

		wfc->write_credits += wfc->credits_to_refill;
	}
}

static void init_lines(struct conv_ftl *conv_ftl)
{
	struct ssdparams *spp = &conv_ftl->ssd->sp;
	struct line_mgmt *lm = &conv_ftl->lm;
	struct line *line;
	int i;

	lm->tt_lines = spp->blks_per_pl;
	NVMEV_ASSERT(lm->tt_lines == spp->tt_lines);
	lm->lines = vmalloc(sizeof(struct line) * lm->tt_lines);

	INIT_LIST_HEAD(&lm->free_line_list);
	INIT_LIST_HEAD(&lm->full_line_list);

	lm->victim_line_pq = pqueue_init(spp->tt_lines, victim_line_cmp_pri, victim_line_get_pri,
					 victim_line_set_pri, victim_line_get_pos,
					 victim_line_set_pos);

	lm->free_line_cnt = 0;
	for (i = 0; i < lm->tt_lines; i++) {
		lm->lines[i] = (struct line){
			.id = i,
			.ipc = 0,
			.vpc = 0,
			.pos = 0,
			.entry = LIST_HEAD_INIT(lm->lines[i].entry),
		};

		/* initialize all the lines as free lines */
		list_add_tail(&lm->lines[i].entry, &lm->free_line_list);
		lm->free_line_cnt++;
	}

	NVMEV_ASSERT(lm->free_line_cnt == lm->tt_lines);
	lm->victim_line_cnt = 0;
	lm->full_line_cnt = 0;
}

static void remove_lines(struct conv_ftl *conv_ftl)
{
	pqueue_free(conv_ftl->lm.victim_line_pq);
	vfree(conv_ftl->lm.lines);
}

static void init_write_flow_control(struct conv_ftl *conv_ftl)
{
	struct write_flow_control *wfc = &(conv_ftl->wfc);
	struct ssdparams *spp = &conv_ftl->ssd->sp;

	wfc->write_credits = spp->pgs_per_line;
	wfc->credits_to_refill = spp->pgs_per_line;
}

static inline void check_addr(int a, int max)
{
	NVMEV_ASSERT(a >= 0 && a < max);
}

static int get_next_free_ruid(struct conv_ftl *conv_ftl, struct fdp_ru_mgmt *rum) //update~
{
#ifdef FDP_DEBUG
        printk("get_next_free_ruid() called -> ");
#endif
        struct ru *retru = NULL;

        retru = QTAILQ_FIRST(&rum->free_ru_list);
        if (!retru) {
                //ftl_err("No free reclaim units left in [%s] !!!!\n", ssd->ssdname);
                return -1;
        }
#ifdef FDP_DEBUG
        printk("new ru: %d\n", retru->id);
#endif
        QTAILQ_REMOVE(&rum->free_ru_list, retru, entry);
        rum->free_ru_cnt--;

        return retru->id;
}

static struct line *get_next_free_line(struct conv_ftl *conv_ftl)
{
	struct line_mgmt *lm = &conv_ftl->lm;
	struct line *curline = list_first_entry_or_null(&lm->free_line_list, struct line, entry);

	if (!curline) {
		NVMEV_ERROR("No free line left in VIRT !!!!\n");
		return NULL;
	}

	list_del_init(&curline->entry);
	lm->free_line_cnt--;
	NVMEV_DEBUG("%s: free_line_cnt %d\n", __func__, lm->free_line_cnt);
	return curline;
}

static struct write_pointer *__get_wp(struct conv_ftl *ftl, uint32_t io_type)
{
	if (io_type == USER_IO) {
		return &ftl->wp;
	} else if (io_type == GC_IO) {
		return &ftl->gc_wp;
	}

	NVMEV_ASSERT(0);
	return NULL;
}

static void prepare_write_pointer(struct conv_ftl *conv_ftl, uint32_t io_type)
{
	struct write_pointer *wp = __get_wp(conv_ftl, io_type);
	struct line *curline = get_next_free_line(conv_ftl);

	NVMEV_ASSERT(wp);
	NVMEV_ASSERT(curline);

	/* wp->curline is always our next-to-write super-block */
	*wp = (struct write_pointer){
		.curline = curline,
		.ch = 0,
		.lun = 0,
		.pg = 0,
		.blk = curline->id,
		.pl = 0,
	};
}

static void advance_fdp_write_pointer(struct conv_ftl *conv_ftl, uint32_t io_type, uint16_t rgid, uint16_t ruhid)
{
        struct ssdparams *spp = &conv_ftl->ssd->sp;
        struct fdp_ru_mgmt *rum = &conv_ftl->ssd->rums[rgid];
        struct ruh *ruh = &conv_ftl->ssd->ruhtbl[ruhid];
        int max_ch = (rgid + 1) * (RG_DEGREE / spp->luns_per_ch);
        int ruid;
        struct ru *ru = NULL;
	if (io_type == GC_IO) {
                if (ruh->ruht == NVME_RUHT_INITIALLY_ISOLATED) {
                        ruid = rum->ii_gc_ruid;
		}
                else { 
                        ruid = ruh->pi_gc_ruids[rgid];
		}
        }
        else {
                ruid = ruh->cur_ruids[rgid];
	}
	ru = &rum->rus[ruid];

#ifdef SMALL_RG
        if (RG_DEGREE > spp->luns_per_ch)
        {
#endif
                check_addr(ru->wp.ch, max_ch);
                ru->wp.ch++;
                if (ru->wp.ch == max_ch) {
                        ru->wp.ch = rgid * (RG_DEGREE / spp->luns_per_ch);
                        check_addr(ru->wp.lun, spp->luns_per_ch);
                        ru->wp.lun++;
                        // in this case, we should go to next lun 
                        if (ru->wp.lun == spp->luns_per_ch) {
                                ru->wp.lun = 0;
                                // go to next page in the block 
                                check_addr(ru->wp.pg, spp->pgs_per_blk);
                                ru->wp.pg++;
                                if (ru->wp.pg == spp->pgs_per_blk) {
                                        ru->wp.pg = 0;
                                        // move current ru to {victim,full} ru list 
                                        if (ru->vpc == spp->pgs_per_ru) {
                                                // all pgs are still valid, move to full ru list 
                                                NVMEV_ASSERT(ru->ipc == 0);
                                                QTAILQ_INSERT_TAIL(&rum->full_ru_list, ru, entry);
                                                rum->full_ru_cnt++;
                                        } else {
                                                NVMEV_ASSERT(ru->vpc >= 0 && ru->vpc < spp->pgs_per_ru);
						NVMEV_ASSERT(ru->ipc > 0);
                                                pqueue_insert(rum->victim_ru_pq, ru);
                                                rum->victim_ru_cnt++;
                                        }
                                        // current ru is used up, pick another empty ru 
                                        check_addr(ru->wp.blk, spp->blks_per_pl);
                                        // ruh history for gc later 
                                         ru->ruhid = ruhid;
                                        if (ru->rut == RU_TYPE_II_GC) {
                                                rum->ii_gc_ruid = get_next_free_ruid(conv_ftl, rum);
                                                rum->rus[rum->ii_gc_ruid].rut = RU_TYPE_II_GC;
                                        }
                                        else if (ru->rut == RU_TYPE_PI_GC) {
                                                ruh->pi_gc_ruids[rgid] = get_next_free_ruid(conv_ftl, rum);
                                                rum->rus[ruh->pi_gc_ruids[rgid]].rut = RU_TYPE_PI_GC;
                                                }
					else {
                                                // update ruhtbl 
                                                ruh->cur_ruids[rgid] = get_next_free_ruid(conv_ftl, rum);
                                                rum->rus[ruh->cur_ruids[rgid]].rut = RU_TYPE_NORMAL;
                                        }
                                        check_addr(ru->wp.blk, spp->blks_per_pl);
                                        // make sure we are starting from page 0 in the ru 
                                        NVMEV_ASSERT(ru->wp.pg == 0);
                                        NVMEV_ASSERT(ru->wp.lun == 0);
                                        NVMEV_ASSERT(ru->wp.ch == rgid * (RG_DEGREE / spp->luns_per_ch));
                                        // TODO: assume # of pl_per_lun is 1, fix later 
                                        NVMEV_ASSERT(ru->wp.pl == 0);
                                }
                        }
                }
#ifdef SMALL_RG
        }
#endif
#ifdef SMALL_RG
        else
        {
                check_addr(ru->wp.lun, spp->luns_per_ch);
                ru->wp.lun++;
                 //move to next page 
                if (ru->wp.lun % RG_DEGREE == 0)
                {
                        ru->wp.lun = 0;
                        check_addr(ru->wp.pg, spp->pgs_per_ch);
                        ru->wp.pg++;
                        if (ru->wp.pg == spp->pgs_per_blk)
                        {
                                ru->wp.pg = 0;
                   //              move current ru to {victim,full} ru list 
                                if (ru->vpc == spp->pgs_per_blk * RG_DEGREE)
                                {
                                        // all pgs are still valid, move to full ru list 
                                        NVMEV_ASSERT(ru->ipc == 0);
                                        QTAILQ_INSERT_TAIL(&rum->full_ru_list, ru, entry);
                                        rum->full_ru_cnt++;
                                }
				else
                                {
                                        // there must be some invalid pages in this ru 
                                        //NVMEV_ASSERT(ru->vpn >= 0 && ru->vpc < RG_DEGREE * spp->pgs_per_blk);
                                        NVMEV_ASSERT(ru->ipc > 0);
                                        pqueue_insert(rum->victim_ru_pq, ru);
                                        rum->victim_ru_cnt++;
                                }
                                // current ru is used up, pick another empty ru 
                                ru->ruhid = ruhid;
                                if (ru->rut == RU_TYPE_II_GC) {
                                        rum->ii_gc_ruid = get_next_free_ruid(conv_ftl, rum);
                                        rum->rus[rum->ii_gc_ruid].rut = RU_TYPE_II_GC;
                                }
                                else if (ru->rut == RU_TYPE_PI_GC) {
                                        ruh->pi_gc_ruids[rgid] = get_next_free_ruid(conv_ftl, rum);
                                        rum->rus[ruh->pi_gc_ruids[rgid]].rut = RU_TYPE_PI_GC;
                                }
                                else {
                                        // update ruhtbl 
                                        ruh->cur_ruids[rgid] = get_next_free_ruid(conv_ftl, rum);
                                        rum->rus[ruh->cur_ruids[rgid]].rut = RU_TYPE_NORMAL;
                                }
                                check_addr(ru->wp.blk, spp->blks_per_pl);
                                // make sure we are starting from page 0 in the ru 
                                NVMEV_ASSERT(ru->wp.pg == 0);
                                NVMEV_ASSERT(ru->wp.lun == 0);
                                // TODO: assume # of pl_per_lun is 1, fix later 
                                NVMEV_ASSERT(ru->wp.pl == 0);
                        }
                }
        }
#endif

}

static void advance_write_pointer(struct conv_ftl *conv_ftl, uint32_t io_type)
{
	struct ssdparams *spp = &conv_ftl->ssd->sp;
	struct line_mgmt *lm = &conv_ftl->lm;
	struct write_pointer *wpp = __get_wp(conv_ftl, io_type);

	NVMEV_DEBUG_VERBOSE("current wpp: ch:%d, lun:%d, pl:%d, blk:%d, pg:%d\n",
			wpp->ch, wpp->lun, wpp->pl, wpp->blk, wpp->pg);

	check_addr(wpp->pg, spp->pgs_per_blk);
	wpp->pg++;
	if ((wpp->pg % spp->pgs_per_oneshotpg) != 0)
		goto out;

	wpp->pg -= spp->pgs_per_oneshotpg;
	check_addr(wpp->ch, spp->nchs);
	wpp->ch++;
	if (wpp->ch != spp->nchs)
		goto out;

	wpp->ch = 0;
	check_addr(wpp->lun, spp->luns_per_ch);
	wpp->lun++;
	/* in this case, we should go to next lun */
	if (wpp->lun != spp->luns_per_ch)
		goto out;

	wpp->lun = 0;
	/* go to next wordline in the block */
	wpp->pg += spp->pgs_per_oneshotpg;
	if (wpp->pg != spp->pgs_per_blk)
		goto out;

	wpp->pg = 0;
	/* move current line to {victim,full} line list */
	if (wpp->curline->vpc == spp->pgs_per_line) {
		/* all pgs are still valid, move to full line list */
		NVMEV_ASSERT(wpp->curline->ipc == 0);
		list_add_tail(&wpp->curline->entry, &lm->full_line_list);
		lm->full_line_cnt++;
		NVMEV_DEBUG_VERBOSE("wpp: move line to full_line_list\n");
	} else {
		NVMEV_DEBUG_VERBOSE("wpp: line is moved to victim list\n");
		NVMEV_ASSERT(wpp->curline->vpc >= 0 && wpp->curline->vpc < spp->pgs_per_line);
		/* there must be some invalid pages in this line */
		NVMEV_ASSERT(wpp->curline->ipc > 0);
		pqueue_insert(lm->victim_line_pq, wpp->curline);
		lm->victim_line_cnt++;
	}
	/* current line is used up, pick another empty line */
	check_addr(wpp->blk, spp->blks_per_pl);
	wpp->curline = get_next_free_line(conv_ftl);
	NVMEV_DEBUG_VERBOSE("wpp: got new clean line %d\n", wpp->curline->id);

	wpp->blk = wpp->curline->id;
	check_addr(wpp->blk, spp->blks_per_pl);

	/* make sure we are starting from page 0 in the super block */
	NVMEV_ASSERT(wpp->pg == 0);
	NVMEV_ASSERT(wpp->lun == 0);
	NVMEV_ASSERT(wpp->ch == 0);
	/* TODO: assume # of pl_per_lun is 1, fix later */
	NVMEV_ASSERT(wpp->pl == 0);
out:
	NVMEV_DEBUG_VERBOSE("advanced wpp: ch:%d, lun:%d, pl:%d, blk:%d, pg:%d (curline %d)\n",
			wpp->ch, wpp->lun, wpp->pl, wpp->blk, wpp->pg, wpp->curline->id);
}

static struct ppa fdp_get_new_page(struct conv_ftl *conv_ftl, uint32_t io_type, uint16_t rgid, uint16_t ruhid)
{
        struct fdp_ru_mgmt *rum = &conv_ftl->ssd->rums[rgid];
        struct ruh* ruh = &conv_ftl->ssd->ruhtbl[ruhid];
        int ruid;
        struct ru *ru;
        struct ppa ppa;

        if (io_type == GC_IO) {
                if (ruh->ruht == NVME_RUHT_INITIALLY_ISOLATED)
                        ruid = rum->ii_gc_ruid;
                else
                        ruid = ruh->pi_gc_ruids[rgid];
        }
        else // normal
                ruid = ruh->cur_ruids[rgid];

        ppa.ppa = 0;

        rum = &conv_ftl->ssd->rums[rgid];
        ru = &rum->rus[ruid];
        ppa.g.ch = ru->wp.ch;
        ppa.g.lun = ru->wp.lun;
        ppa.g.pg = ru->wp.pg;
        ppa.g.blk = ru->wp.blk;
        ppa.g.pl = ru->wp.pl;
        return ppa;
}

static struct ppa get_new_page(struct conv_ftl *conv_ftl, uint32_t io_type)
{
	struct ppa ppa;
	struct write_pointer *wp = __get_wp(conv_ftl, io_type);

	ppa.ppa = 0;
	ppa.g.ch = wp->ch;
	ppa.g.lun = wp->lun;
	ppa.g.pg = wp->pg;
	ppa.g.blk = wp->blk;
	ppa.g.pl = wp->pl;

	NVMEV_ASSERT(ppa.g.pl == 0);

	return ppa;
}

static void init_maptbl(struct conv_ftl *conv_ftl)
{
	int i;
	struct ssdparams *spp = &conv_ftl->ssd->sp;

	conv_ftl->maptbl = vmalloc(sizeof(struct ppa) * spp->tt_pgs);
	for (i = 0; i < spp->tt_pgs; i++) {
		conv_ftl->maptbl[i].ppa = UNMAPPED_PPA;
	}
}

static void remove_maptbl(struct conv_ftl *conv_ftl)
{
	vfree(conv_ftl->maptbl);
}

static void init_rmap(struct conv_ftl *conv_ftl)
{
	int i;
	struct ssdparams *spp = &conv_ftl->ssd->sp;

	conv_ftl->rmap = vmalloc(sizeof(uint64_t) * spp->tt_pgs);
	for (i = 0; i < spp->tt_pgs; i++) {
		conv_ftl->rmap[i] = INVALID_LPN;
	}
}

static inline int victim_ru_cmp_pri(pqueue_pri_t next, pqueue_pri_t curr)//update~
{
    return (next > curr);
}

static inline pqueue_pri_t victim_ru_get_pri(void *a)
{
    return ((struct ru *)a)->vpc;
}

static inline void victim_ru_set_pri(void *a, pqueue_pri_t pri)
{
    ((struct ru *)a)->vpc = pri;
}

static inline size_t victim_ru_get_pos(void *a)
{
    return ((struct ru *)a)->pos;
}

static inline void victim_ru_set_pos(void *a, size_t pos)
{
    ((struct ru *)a)->pos = pos;
}                                                                       //~update

static void init_fdp_ru_mgmts(struct conv_ftl *conv_ftl)
{
       	struct ssdparams *spp = &conv_ftl->ssd->sp;
        struct fdp_ru_mgmt *rum = NULL;
        struct ru *ru = NULL;
        int nrg = spp->tt_luns / RG_DEGREE;
        int blkoff;

	conv_ftl->ssd->rums = kzalloc(sizeof(struct fdp_ru_mgmt) * nrg, GFP_KERNEL);	
	
	for (int i = 0; i < nrg; i++) {
                rum = &conv_ftl->ssd->rums[i];
                rum->tt_rus = spp->blks_per_lun;
                //assert(rum->tt_rus == spp->blks_per_lun);
                //rum->rus = g_malloc0(sizeof(struct ru) * rum->tt_rus);
                rum->rus = kzalloc(sizeof(struct ru) * rum->tt_rus, GFP_KERNEL);
                QTAILQ_INIT(&rum->free_ru_list);
                rum->victim_ru_pq = pqueue_init(spp->tt_blks, victim_ru_cmp_pri, victim_ru_get_pri, victim_ru_set_pri, victim_ru_get_pos, victim_ru_set_pos);
                QTAILQ_INIT(&rum->full_ru_list);
		
		rum->free_ru_cnt = 0;

		for (int j = 0; j < rum->tt_rus; j++) {
                        ru = &rum->rus[j];
                        ru->id = j;
                        ru->wp.ch = i * RG_DEGREE / spp->luns_per_ch;
                        ru->wp.lun = i * RG_DEGREE % spp->luns_per_ch;
                        ru->wp.pl = 0;
                        ru->wp.blk = j;
                        ru->wp.pg = 0;
                        ru->ipc = 0;
                        ru->vpc = 0;
                        ru->pos = 0;
                        ru->rut = RU_TYPE_NORMAL;
                        /* ruh history for gc */
                        if (j < MAX_RUHS)
                                ru->ruhid = j;

                        blkoff = j % spp->blks_per_pl;
                        //ru->blks = gmalloc0(sizeof(struct nand_block*) * RG_DEGREE);
                        for (int k = 0; k < RG_DEGREE; k++) {
                                int cur_ch = ru->wp.ch + k / spp->luns_per_ch;
                                int cur_lun = (ru->wp.lun + k) % spp->luns_per_ch;

                                ru->blks[k] = &conv_ftl->ssd->ch[cur_ch].lun[cur_lun].pl[0].blk[blkoff];
                        }

                        /* initialize all the reclaim units as free reclaim units */
                        QTAILQ_INSERT_TAIL(&rum->free_ru_list, ru, entry);
                        rum->free_ru_cnt++;
                }
                //ftl_assert(rum->free_ru_cnt == rum->tt_rus);
                rum->victim_ru_cnt = 0;
                rum->full_ru_cnt = 0;
	}
}

static void init_fdp_ruhtbl(struct conv_ftl *conv_ftl, struct nvmev_ns *ns)
{
	struct ruh *ruh = NULL;
        struct fdp_ru_mgmt *rum = NULL;

	conv_ftl->ssd->fdp_enabled = ns->endgrps.fdp.enabled;
        conv_ftl->ssd->ruhtbl = kzalloc(sizeof(struct ruh) * ns->endgrps.fdp.nruh, GFP_KERNEL);
        for (int i = 0; i < ns->endgrps.fdp.nruh; i++) {
                ruh = &conv_ftl->ssd->ruhtbl[i];
                ruh->ruht = ns->endgrps.fdp.ruhs[i].ruht;
                ruh->cur_ruids = kzalloc(sizeof(int) * ns->endgrps.fdp.nrg, GFP_KERNEL);
                ruh->pi_gc_ruids = kzalloc(sizeof(int) * ns->endgrps.fdp.nrg, GFP_KERNEL);
                for (int j = 0; j < ns->endgrps.fdp.nrg; j++)  {
                        rum = &conv_ftl->ssd->rums[j];
                        ruh->cur_ruids[j] = get_next_free_ruid(conv_ftl, rum);
                }
        }
	/* reserve one ru for initially isolated gc */
        for (int i = 0; i < ns->endgrps.fdp.nrg; i++) {
                rum = &conv_ftl->ssd->rums[i];
                rum->ii_gc_ruid = get_next_free_ruid(conv_ftl, rum);
                rum->rus[rum->ii_gc_ruid].rut = RU_TYPE_II_GC;
        }

	        /* reserve rus for persistently isolated gc */
        /*
        for (int i = 0; i < endgrp->fdp.nrg; i++) {
                int pi_gc_ruid;
                rum = &ssd->rums[i];

                pi_gc_ruid = get_next_free_ruid(ssd, rum);
                ssd->ruhtbl[0].pi_gc_ruids[i] = pi_gc_ruid;
                rum->rus[pi_gc_ruid].rut = RU_TYPE_PI_GC;

                pi_gc_ruid = get_next_free_ruid(ssd, rum);
                ssd->ruhtbl[1].pi_gc_ruids[i] = pi_gc_ruid;
                rum->rus[pi_gc_ruid].rut = RU_TYPE_PI_GC;

                pi_gc_ruid = get_next_free_ruid(ssd, rum);
                ssd->ruhtbl[2].pi_gc_ruids[i] = pi_gc_ruid;
                rum->rus[pi_gc_ruid].rut = RU_TYPE_PI_GC;

                pi_gc_ruid = get_next_free_ruid(ssd, rum);
                ssd->ruhtbl[3].pi_gc_ruids[i] = pi_gc_ruid;
                rum->rus[pi_gc_ruid].rut = RU_TYPE_PI_GC;
        }*/

}

static void remove_rmap(struct conv_ftl *conv_ftl)
{
	vfree(conv_ftl->rmap);
}

static void conv_init_ftl(struct conv_ftl *conv_ftl, struct convparams *cpp, struct ssd *ssd, struct nvmev_ns *ns)
{
	/*copy convparams*/
	conv_ftl->cp = *cpp;

	conv_ftl->ssd = ssd;

	conv_ftl->ssd->endgrp = &ns->endgrps;

	/* initialize maptbl */
	init_maptbl(conv_ftl); // mapping table

	/* initialize rmap */
	init_rmap(conv_ftl); // reverse mapping table (?)

	/* initialize all the lines */
	init_lines(conv_ftl);

	/* initialize write pointer, this is how we allocate new pages for writes */
	prepare_write_pointer(conv_ftl, USER_IO);
	prepare_write_pointer(conv_ftl, GC_IO);

	init_write_flow_control(conv_ftl);

	/* intialize fdp */
	init_fdp_ru_mgmts(conv_ftl);
	init_fdp_ruhtbl(conv_ftl, ns);

	NVMEV_INFO("Init FTL instance with %d channels (%ld pages)\n", conv_ftl->ssd->sp.nchs,
		   conv_ftl->ssd->sp.tt_pgs);

	return;
}

static void conv_remove_ftl(struct conv_ftl *conv_ftl)
{
	remove_lines(conv_ftl);
	remove_rmap(conv_ftl);
	remove_maptbl(conv_ftl);
}

static void conv_init_params(struct convparams *cpp)
{
	cpp->op_area_pcent = OP_AREA_PERCENT;
	cpp->gc_thres_lines = 2; /* Need only two lines.(host write, gc)*/
	cpp->gc_thres_lines_high = 2; /* Need only two lines.(host write, gc)*/
	cpp->enable_gc_delay = 1;
	cpp->pba_pcent = (int)((1 + cpp->op_area_pcent) * 100);

	cpp->gc_thres_rus = 20;
	cpp->gc_thres_rus_high = 20;
}

static int cal_rgif(int nrg)            // update ~
{
        int n = nrg;
        int cnt = 0;

        while (n > 1)
        {
                n = n / 2;
                cnt++;
        }

        return cnt;
}                                       // ~ update

static void conv_init_endgrps(struct nvmev_ns *ns, struct ssdparams *spp)
{
	struct NvmeRuHandle *ruh = NULL;
        const uint8_t lba_index = NVME_ID_NS_FLBAS_INDEX(0);
        const uint8_t data_shift = 9;
	ns->num_endgrps = 1;

	for (int i = 0; i < ns->num_endgrps; i++)
        {
		//now num_endgrps is 1 as a default,
		//that's why ns->endgrps is not a pointer
		ns->endgrps.fdp.runs = RG_DEGREE * spp->pgs_per_blk * spp->secs_per_pg * spp->secsz;
		ns->endgrps.fdp.nrg = spp->nchs * spp->luns_per_ch / RG_DEGREE;
	//	printk("ns->endgrps.fdp.nrg %d\n",ns->endgrps.fdp.nrg);
		ns->endgrps.fdp.rgif = cal_rgif(ns->endgrps.fdp.nrg);
		ns->endgrps.fdp.nruh = MAX_RUHS;

		ns->endgrps.fdp.hbmw = 0;
		ns->endgrps.fdp.mbmw = 0;
		ns->endgrps.fdp.mbe = 0;

		ns->endgrps.fdp.ruhs = kzalloc(sizeof(struct NvmeRuHandle) * ns->endgrps.fdp.nruh, GFP_KERNEL);

		for (int ruhid = 0; ruhid < ns->endgrps.fdp.nruh; ruhid++)
		{
	//		printk("ruhid %d\n",ruhid);
			ns->endgrps.fdp.ruhs[ruhid] = (struct NvmeRuHandle)
			{
				.ruht = NVME_RUHT_INITIALLY_ISOLATED,
                        	.ruha = NVME_RUHA_HOST,
                        	.ruamw = ns->endgrps.fdp.runs >> data_shift,
                        	.lbafi = lba_index,
                        	.rus = kzalloc(sizeof(struct NvmeReclaimUnit) * ns->endgrps.fdp.nrg, GFP_KERNEL)
			};
			for (int rgid = 0; rgid < ns->endgrps.fdp.nrg; rgid++)
			{
                       		ns->endgrps.fdp.ruhs[ruhid].rus[rgid].ruamw = ns->endgrps.fdp.ruhs[ruhid].ruamw;
	//			printk("ns->endgrps.fdp.ruhs[%d].rus[%d].ruamw : %lld\n",ruhid , rgid, ns->endgrps.fdp.ruhs[ruhid].ruamw);
			}
			ns->endgrps.fdp.enabled = true;
		}
	}
	ns->fdp_ns.nphs = ns->endgrps.fdp.nruh;
        ns->fdp_ns.phs = kzalloc(sizeof(uint16_t) * ns->fdp_ns.nphs, GFP_KERNEL);

	for (int i = 0; i < ns->fdp_ns.nphs; i++) {
                ns->fdp_ns.phs[i] = i;
		printk("phs : %d\n",ns->fdp_ns.phs[i]);
	}
}

void conv_init_namespace(struct nvmev_ns *ns, uint32_t id, uint64_t size, void *mapped_addr, uint32_t cpu_nr_dispatcher)
{
	struct ssdparams spp;
	struct convparams cpp;
	struct conv_ftl *conv_ftls;
	struct ssd *ssd;
	uint32_t i;
	const uint32_t nr_parts = SSD_PARTITIONS;

	ssd_init_params(&spp, size, nr_parts);
	conv_init_endgrps(ns, &spp);             //update
	conv_init_params(&cpp);

	conv_ftls = kmalloc(sizeof(struct conv_ftl) * nr_parts, GFP_KERNEL);

	for (i = 0; i < nr_parts; i++) {
		ssd = kmalloc(sizeof(struct ssd), GFP_KERNEL);
		ssd_init(ssd, &spp, cpu_nr_dispatcher);
		conv_init_ftl(&conv_ftls[i], &cpp, ssd, ns);
	}

	/* PCIe, Write buffer are shared by all instances*/
	for (i = 1; i < nr_parts; i++) {
		kfree(conv_ftls[i].ssd->pcie->perf_model);
		kfree(conv_ftls[i].ssd->pcie);
		kfree(conv_ftls[i].ssd->write_buffer);

		conv_ftls[i].ssd->pcie = conv_ftls[0].ssd->pcie;
		conv_ftls[i].ssd->write_buffer = conv_ftls[0].ssd->write_buffer;
	}

	ns->id = id;
	ns->csi = NVME_CSI_NVM;
	ns->nr_parts = nr_parts;
	ns->ftls = (void *)conv_ftls;
	ns->size = (uint64_t)((size * 100) / cpp.pba_pcent);
	ns->mapped = mapped_addr;
	/*register io command handler*/
	ns->proc_io_cmd = conv_proc_nvme_io_cmd;

	NVMEV_INFO("FTL physical space: %lld, logical space: %lld (physical/logical * 100 = %d)\n",
		   size, ns->size, cpp.pba_pcent);

	return;
}

void conv_remove_namespace(struct nvmev_ns *ns)
{
	struct conv_ftl *conv_ftls = (struct conv_ftl *)ns->ftls;
	const uint32_t nr_parts = SSD_PARTITIONS;
	uint32_t i;

	/* PCIe, Write buffer are shared by all instances*/
	for (i = 1; i < nr_parts; i++) {
		/*
		 * These were freed from conv_init_namespace() already.
		 * Mark these NULL so that ssd_remove() skips it.
		 */
		conv_ftls[i].ssd->pcie = NULL;
		conv_ftls[i].ssd->write_buffer = NULL;
	}

	for (i = 0; i < nr_parts; i++) {
		conv_remove_ftl(&conv_ftls[i]);
		ssd_remove(conv_ftls[i].ssd);
		kfree(conv_ftls[i].ssd);
	}

	kfree(conv_ftls);
	ns->ftls = NULL;
}

static inline bool valid_ppa(struct conv_ftl *conv_ftl, struct ppa *ppa)
{
	struct ssdparams *spp = &conv_ftl->ssd->sp;
	int ch = ppa->g.ch;
	int lun = ppa->g.lun;
	int pl = ppa->g.pl;
	int blk = ppa->g.blk;
	int pg = ppa->g.pg;
	//int sec = ppa->g.sec;

	if (ch < 0 || ch >= spp->nchs)
		return false;
	if (lun < 0 || lun >= spp->luns_per_ch)
		return false;
	if (pl < 0 || pl >= spp->pls_per_lun)
		return false;
	if (blk < 0 || blk >= spp->blks_per_pl)
		return false;
	if (pg < 0 || pg >= spp->pgs_per_blk)
		return false;

	return true;
}

static inline bool valid_lpn(struct conv_ftl *conv_ftl, uint64_t lpn)
{
	return (lpn < conv_ftl->ssd->sp.tt_pgs);
}

static inline bool mapped_ppa(struct ppa *ppa)
{
	return !(ppa->ppa == UNMAPPED_PPA);
}

static inline struct line *get_line(struct conv_ftl *conv_ftl, struct ppa *ppa)
{
	return &(conv_ftl->lm.lines[ppa->g.blk]);
}

/* update SSD status about one page from PG_VALID -> PG_VALID */
static void mark_page_invalid(struct conv_ftl *conv_ftl, struct ppa *ppa)
{
	struct ssdparams *spp = &conv_ftl->ssd->sp;
	struct line_mgmt *lm = &conv_ftl->lm;
	struct nand_block *blk = NULL;
	struct nand_page *pg = NULL;
	bool was_full_line = false;
	struct line *line;

	/* update corresponding page status */
	pg = get_pg(conv_ftl->ssd, ppa);
	NVMEV_ASSERT(pg->status == PG_VALID);
	pg->status = PG_INVALID;

	/* update corresponding block status */
	blk = get_blk(conv_ftl->ssd, ppa);
	NVMEV_ASSERT(blk->ipc >= 0 && blk->ipc < spp->pgs_per_blk);
	blk->ipc++;
	NVMEV_ASSERT(blk->vpc > 0 && blk->vpc <= spp->pgs_per_blk);
	blk->vpc--;

	/* update corresponding line status */
	line = get_line(conv_ftl, ppa);
	NVMEV_ASSERT(line->ipc >= 0 && line->ipc < spp->pgs_per_line);
	if (line->vpc == spp->pgs_per_line) {
		NVMEV_ASSERT(line->ipc == 0);
		was_full_line = true;
	}
	line->ipc++;
	NVMEV_ASSERT(line->vpc > 0 && line->vpc <= spp->pgs_per_line);
	/* Adjust the position of the victime line in the pq under over-writes */
	if (line->pos) {
		/* Note that line->vpc will be updated by this call */
		pqueue_change_priority(lm->victim_line_pq, line->vpc - 1, line);
	} else {
		line->vpc--;
	}

	if (was_full_line) {
		/* move line: "full" -> "victim" */
		list_del_init(&line->entry);
		lm->full_line_cnt--;
		pqueue_insert(lm->victim_line_pq, line);
		lm->victim_line_cnt++;
	}
}

static void mark_page_valid(struct conv_ftl *conv_ftl, struct ppa *ppa)
{
	struct ssdparams *spp = &conv_ftl->ssd->sp;
	struct nand_block *blk = NULL;
	struct nand_page *pg = NULL;
	struct line *line;

	/* update page status */
	pg = get_pg(conv_ftl->ssd, ppa);
	NVMEV_ASSERT(pg->status == PG_FREE);
	pg->status = PG_VALID;

	/* update corresponding block status */
	blk = get_blk(conv_ftl->ssd, ppa);
	NVMEV_ASSERT(blk->vpc >= 0 && blk->vpc < spp->pgs_per_blk);
	blk->vpc++;

	/* update corresponding line status */
	line = get_line(conv_ftl, ppa);
	NVMEV_ASSERT(line->vpc >= 0 && line->vpc < spp->pgs_per_line);
	line->vpc++;
}

static void mark_block_free(struct conv_ftl *conv_ftl, struct ppa *ppa)
{
	struct ssdparams *spp = &conv_ftl->ssd->sp;
	struct nand_block *blk = get_blk(conv_ftl->ssd, ppa);
	struct nand_page *pg = NULL;
	int i;

	for (i = 0; i < spp->pgs_per_blk; i++) {
		/* reset page status */
		pg = &blk->pg[i];
		NVMEV_ASSERT(pg->nsecs == spp->secs_per_pg);
		pg->status = PG_FREE;
	}

	/* reset block status */
	NVMEV_ASSERT(blk->npgs == spp->pgs_per_blk);
	blk->ipc = 0;
	blk->vpc = 0;
	blk->erase_cnt++;
}

static void gc_read_page(struct conv_ftl *conv_ftl, struct ppa *ppa)
{
	struct ssdparams *spp = &conv_ftl->ssd->sp;
	struct convparams *cpp = &conv_ftl->cp;
	/* advance conv_ftl status, we don't care about how long it takes */
	if (cpp->enable_gc_delay) {
		struct nand_cmd gcr = {
			.type = GC_IO,
			.cmd = NAND_READ,
			.stime = 0,
			.xfer_size = spp->pgsz,
			.interleave_pci_dma = false,
			.ppa = ppa,
		};
		ssd_advance_nand(conv_ftl->ssd, &gcr);
	}
}

static uint64_t fdp_gc_write_page(struct conv_ftl *conv_ftl, struct ppa *old_ppa, uint16_t rgid, uint16_t ruhid)
{
        struct ssdparams *spp = &conv_ftl->ssd->sp;
        struct convparams *cpp = &conv_ftl->cp;
        struct ppa new_ppa;
        uint64_t lpn = get_rmap_ent(conv_ftl, old_ppa);

        NVMEV_ASSERT(valid_lpn(conv_ftl, lpn));
        new_ppa = fdp_get_new_page(conv_ftl, GC_IO, rgid, ruhid);       //update
        /* update maptbl */
        set_maptbl_ent(conv_ftl, lpn, &new_ppa);
        /* update rmap */
        set_rmap_ent(conv_ftl, lpn, &new_ppa);

        mark_page_valid(conv_ftl, &new_ppa);

        /* need to advance the write pointer here */
        advance_fdp_write_pointer(conv_ftl, GC_IO, rgid, ruhid);        //update

        if (cpp->enable_gc_delay) {
                struct nand_cmd gcw = {
                        .type = GC_IO,
                        .cmd = NAND_NOP,
                        .stime = 0,
                        .interleave_pci_dma = false,
                        .ppa = &new_ppa,
                };
                if (last_pg_in_wordline(conv_ftl, &new_ppa)) {
                        gcw.cmd = NAND_WRITE;
                        gcw.xfer_size = spp->pgsz * spp->pgs_per_oneshotpg;
                }

                ssd_advance_nand(conv_ftl->ssd, &gcw);
        }

        return 0;
}

/* move valid page data (already in DRAM) from victim line to a new page */
static uint64_t gc_write_page(struct conv_ftl *conv_ftl, struct ppa *old_ppa)
{
	struct ssdparams *spp = &conv_ftl->ssd->sp;
	struct convparams *cpp = &conv_ftl->cp;
	struct ppa new_ppa;
	uint64_t lpn = get_rmap_ent(conv_ftl, old_ppa);

	NVMEV_ASSERT(valid_lpn(conv_ftl, lpn));
	new_ppa = get_new_page(conv_ftl, GC_IO);
	/* update maptbl */
	set_maptbl_ent(conv_ftl, lpn, &new_ppa);
	/* update rmap */
	set_rmap_ent(conv_ftl, lpn, &new_ppa);

	mark_page_valid(conv_ftl, &new_ppa);

	/* need to advance the write pointer here */
	advance_write_pointer(conv_ftl, GC_IO);

	if (cpp->enable_gc_delay) {
		struct nand_cmd gcw = {
			.type = GC_IO,
			.cmd = NAND_NOP,
			.stime = 0,
			.interleave_pci_dma = false,
			.ppa = &new_ppa,
		};
		if (last_pg_in_wordline(conv_ftl, &new_ppa)) {
			gcw.cmd = NAND_WRITE;
			gcw.xfer_size = spp->pgsz * spp->pgs_per_oneshotpg;
		}

		ssd_advance_nand(conv_ftl->ssd, &gcw);
	}

	/* advance per-ch gc_endtime as well */
#if 0
	new_ch = get_ch(conv_ftl, &new_ppa);
	new_ch->gc_endtime = new_ch->next_ch_avail_time;

	new_lun = get_lun(conv_ftl, &new_ppa);
	new_lun->gc_endtime = new_lun->next_lun_avail_time;
#endif

	return 0;
}

static struct line *select_victim_line(struct conv_ftl *conv_ftl, bool force)
{
	struct ssdparams *spp = &conv_ftl->ssd->sp;
	struct line_mgmt *lm = &conv_ftl->lm;
	struct line *victim_line = NULL;

	victim_line = pqueue_peek(lm->victim_line_pq);
	if (!victim_line) {
		return NULL;
	}

	if (!force && (victim_line->vpc > (spp->pgs_per_line / 8))) {
		return NULL;
	}

	pqueue_pop(lm->victim_line_pq);
	victim_line->pos = 0;
	lm->victim_line_cnt--;

	/* victim_line is a danggling node now */
	return victim_line;
}

/* here ppa identifies the block we want to clean */
static void clean_one_block(struct conv_ftl *conv_ftl, struct ppa *ppa)
{
	struct ssdparams *spp = &conv_ftl->ssd->sp;
	struct nand_page *pg_iter = NULL;
	int cnt = 0;
	int pg;

	for (pg = 0; pg < spp->pgs_per_blk; pg++) {
		ppa->g.pg = pg;
		pg_iter = get_pg(conv_ftl->ssd, ppa);
		/* there shouldn't be any free page in victim blocks */
		NVMEV_ASSERT(pg_iter->status != PG_FREE);
		if (pg_iter->status == PG_VALID) {
			gc_read_page(conv_ftl, ppa);
			/* delay the maptbl update until "write" happens */
			gc_write_page(conv_ftl, ppa);
			cnt++;
		}
	}

	NVMEV_ASSERT(get_blk(conv_ftl->ssd, ppa)->vpc == cnt);
}

/* here ppa identifies the block we want to clean */
static int fdp_clean_one_block(struct conv_ftl *conv_ftl, struct ppa *ppa, uint16_t rgid, uint16_t ruhid)
{
        struct ssdparams *spp = &conv_ftl->ssd->sp;
        struct nand_page *pg_iter = NULL;
        int cnt = 0;
        int pg;

        for (pg = 0; pg < spp->pgs_per_blk; pg++) {
                ppa->g.pg = pg;
                pg_iter = get_pg(conv_ftl->ssd, ppa);
                /* there shouldn't be any free page in victim blocks */
                NVMEV_ASSERT(pg_iter->status != PG_FREE);
                if (pg_iter->status == PG_VALID) {
                        gc_read_page(conv_ftl, ppa);
                        /* delay the maptbl update until "write" happens */
                        fdp_gc_write_page(conv_ftl, ppa, rgid, ruhid);
                        cnt++;
                }
        }

        NVMEV_ASSERT(get_blk(conv_ftl->ssd, ppa)->vpc == cnt);
        return cnt;
}

/* here ppa identifies the block we want to clean */
static void clean_one_flashpg(struct conv_ftl *conv_ftl, struct ppa *ppa)
{
	struct ssdparams *spp = &conv_ftl->ssd->sp;
	struct convparams *cpp = &conv_ftl->cp;
	struct nand_page *pg_iter = NULL;
	int cnt = 0, i = 0;
	uint64_t completed_time = 0;
	struct ppa ppa_copy = *ppa;

	for (i = 0; i < spp->pgs_per_flashpg; i++) {
		pg_iter = get_pg(conv_ftl->ssd, &ppa_copy);
		/* there shouldn't be any free page in victim blocks */
		NVMEV_ASSERT(pg_iter->status != PG_FREE);
		if (pg_iter->status == PG_VALID)
			cnt++;

		ppa_copy.g.pg++;
	}

	ppa_copy = *ppa;

	if (cnt <= 0)
		return;

	if (cpp->enable_gc_delay) {
		struct nand_cmd gcr = {
			.type = GC_IO,
			.cmd = NAND_READ,
			.stime = 0,
			.xfer_size = spp->pgsz * cnt,
			.interleave_pci_dma = false,
			.ppa = &ppa_copy,
		};
		completed_time = ssd_advance_nand(conv_ftl->ssd, &gcr);
	}

	for (i = 0; i < spp->pgs_per_flashpg; i++) {
		pg_iter = get_pg(conv_ftl->ssd, &ppa_copy);

		/* there shouldn't be any free page in victim blocks */
		if (pg_iter->status == PG_VALID) {
			/* delay the maptbl update until "write" happens */
			gc_write_page(conv_ftl, &ppa_copy);
		}

		ppa_copy.g.pg++;
	}
}

static void mark_line_free(struct conv_ftl *conv_ftl, struct ppa *ppa)
{
	struct line_mgmt *lm = &conv_ftl->lm;
	struct line *line = get_line(conv_ftl, ppa);
	line->ipc = 0;
	line->vpc = 0;
	/* move this line to free line list */
	list_add_tail(&line->entry, &lm->free_line_list);
	lm->free_line_cnt++;
}

static struct ru *select_victim_ru(struct conv_ftl *conv_ftl, bool force, int rgid)
{
    struct fdp_ru_mgmt *rum = &conv_ftl->ssd->rums[rgid];
    struct ru *victim_ru = NULL;

    victim_ru = pqueue_peek(rum->victim_ru_pq);
    if (!victim_ru) {
        return NULL;
    }

    if (!force && victim_ru->ipc < conv_ftl->ssd->sp.pgs_per_ru / 8) {
        return NULL;
    }

    pqueue_pop(rum->victim_ru_pq);
    victim_ru->pos = 0;
    rum->victim_ru_cnt--;

    /* victim_ru is a danggling node now */
    return victim_ru;
}

bool gc = 0;
static int do_fdp_gc(struct conv_ftl *conv_ftl, uint16_t rgid, bool force, struct nvmev_request *req)
{
	if (!gc)
                printk("do_fdp_gc() called\n");

	struct ru *victim_ru = NULL;
        struct ssdparams *spp = &conv_ftl->ssd->sp;
        struct nand_lun *lunp;
        struct ppa ppa;
        struct fdp_ru_mgmt *rum = &conv_ftl->ssd->rums[rgid];
        int start_lunidx = rgid * RG_DEGREE;
        int ruhid;
        int flashpg;

	int gc_pgs = 0;

	victim_ru = select_victim_ru(conv_ftl, force, rgid);
        if (!victim_ru) {
                return -1;
        }
        ppa.g.blk = victim_ru->id;
        ruhid = victim_ru->ruhid;

        NVMEV_DEBUG_VERBOSE("GC-ing line:%d,ipc=%d,victim=%d,full=%d,free=%d\n", ppa.g.blk, victim_line->ipc, ssd->lm.victim_line_cnt, ssd->lm.full_line_cnt, ssd->lm.free_line_cnt);	
#ifdef FDP_DEBUG
        printk("rgid: %d\n", rgid);
        printk("ruhid: %d\n", ruhid);
        printk("victim_ru id: %d\n", victim_ru->id);
        printk("victim_ru->ipc: %d\n", victim_ru->ipc);
        printk("victim_ru->vpc: %d\n", victim_ru->vpc);
#endif
	for (int lunidx = start_lunidx; lunidx < start_lunidx + RG_DEGREE; lunidx++) {
                ppa.g.ch = lunidx / spp->luns_per_ch;
                ppa.g.lun = lunidx % spp->luns_per_ch;
                ppa.g.pl = 0;
                lunp = get_lun(conv_ftl->ssd, &ppa);
                gc_pgs += fdp_clean_one_block(conv_ftl, &ppa, rgid, ruhid);  //update

                if (flashpg == (spp->flashpgs_per_blk - 1)) {
                        struct convparams *cpp = &conv_ftl->cp;
                        mark_block_free(conv_ftl, &ppa);
                        for (int lunidx = start_lunidx; lunidx < start_lunidx + RG_DEGREE; lunidx++) {
                                if (cpp->enable_gc_delay) {
                                        struct nand_cmd gce = {
                                                .type = GC_IO,
                                                .cmd = NAND_ERASE,
                                                .stime = 0,
                                                .interleave_pci_dma = false,
                                                .ppa = &ppa,
                                        };
                                        ssd_advance_nand(conv_ftl->ssd, &gce);
                                 }
                                lunp->gc_endtime = lunp->next_lun_avail_time;
                        }
                }
        }
#ifdef WAF_TEST
        req->ns->ctrl->gc_writes += gc_pgs * 8;
#endif
#ifdef DEVICE_UTIL_DEBUG
        spp->tt_valid_pgs += gc_pgs;
#endif
/* reset wp of victim ru */
        victim_ru->wp.ch = start_lunidx / spp->luns_per_ch;
        victim_ru->wp.lun = start_lunidx % spp->luns_per_ch;
        victim_ru->wp.pl = 0;
        victim_ru->wp.blk = victim_ru->id;
        victim_ru->wp.pg = 0;

    /* update ru status */
        victim_ru->ipc = 0;
        victim_ru->vpc = 0;
        QTAILQ_INSERT_TAIL(&rum->free_ru_list, victim_ru, entry);
        rum->free_ru_cnt++;

        return 0;

}

static int do_gc(struct conv_ftl *conv_ftl, bool force)
{
	struct line *victim_line = NULL;
	struct ssdparams *spp = &conv_ftl->ssd->sp;
	struct ppa ppa;
	int flashpg;

	victim_line = select_victim_line(conv_ftl, force);
	if (!victim_line) {
		return -1;
	}

	ppa.g.blk = victim_line->id;
	NVMEV_DEBUG_VERBOSE("GC-ing line:%d,ipc=%d(%d),victim=%d,full=%d,free=%d\n", ppa.g.blk,
		    victim_line->ipc, victim_line->vpc, conv_ftl->lm.victim_line_cnt,
		    conv_ftl->lm.full_line_cnt, conv_ftl->lm.free_line_cnt);

	conv_ftl->wfc.credits_to_refill = victim_line->ipc;

	/* copy back valid data */
	for (flashpg = 0; flashpg < spp->flashpgs_per_blk; flashpg++) {
		int ch, lun;

		ppa.g.pg = flashpg * spp->pgs_per_flashpg;
		for (ch = 0; ch < spp->nchs; ch++) {
			for (lun = 0; lun < spp->luns_per_ch; lun++) {
				struct nand_lun *lunp;

				ppa.g.ch = ch;
				ppa.g.lun = lun;
				ppa.g.pl = 0;
				lunp = get_lun(conv_ftl->ssd, &ppa);
				clean_one_flashpg(conv_ftl, &ppa);

				if (flashpg == (spp->flashpgs_per_blk - 1)) {
					struct convparams *cpp = &conv_ftl->cp;

					mark_block_free(conv_ftl, &ppa);

					if (cpp->enable_gc_delay) {
						struct nand_cmd gce = {
							.type = GC_IO,
							.cmd = NAND_ERASE,
							.stime = 0,
							.interleave_pci_dma = false,
							.ppa = &ppa,
						};
						ssd_advance_nand(conv_ftl->ssd, &gce);
					}

					lunp->gc_endtime = lunp->next_lun_avail_time;
				}
			}
		}
	}

	/* update line status */
	mark_line_free(conv_ftl, &ppa);

	return 0;
}

static void foreground_gc(struct conv_ftl *conv_ftl)
{
	if (should_gc_high(conv_ftl)) {
		NVMEV_DEBUG_VERBOSE("should_gc_high passed");
		/* perform GC here until !should_gc(conv_ftl) */
		do_gc(conv_ftl, true);
	}
}

static bool is_same_flash_page(struct conv_ftl *conv_ftl, struct ppa ppa1, struct ppa ppa2)
{
	struct ssdparams *spp = &conv_ftl->ssd->sp;
	uint32_t ppa1_page = ppa1.g.pg / spp->pgs_per_flashpg;
	uint32_t ppa2_page = ppa2.g.pg / spp->pgs_per_flashpg;

	return (ppa1.h.blk_in_ssd == ppa2.h.blk_in_ssd) && (ppa1_page == ppa2_page);
}

static bool conv_read(struct nvmev_ns *ns, struct nvmev_request *req, struct nvmev_result *ret)
{
	struct conv_ftl *conv_ftls = (struct conv_ftl *)ns->ftls;
	struct conv_ftl *conv_ftl = &conv_ftls[0];
	/* spp are shared by all instances*/
	struct ssdparams *spp = &conv_ftl->ssd->sp;

	struct nvme_command *cmd = req->cmd;
	uint64_t lba = cmd->rw.slba;
	uint64_t nr_lba = (cmd->rw.length + 1);
	uint64_t start_lpn = lba / spp->secs_per_pg;
	uint64_t end_lpn = (lba + nr_lba - 1) / spp->secs_per_pg;
	uint64_t lpn;
	uint64_t nsecs_start = req->nsecs_start;
	uint64_t nsecs_completed, nsecs_latest = nsecs_start;
	uint32_t xfer_size, i;
	uint32_t nr_parts = ns->nr_parts;

	struct ppa prev_ppa;
	struct nand_cmd srd = {
		.type = USER_IO,
		.cmd = NAND_READ,
		.stime = nsecs_start,
		.interleave_pci_dma = true,
	};

	NVMEV_ASSERT(conv_ftls);
	NVMEV_DEBUG_VERBOSE("%s: start_lpn=%lld, len=%lld, end_lpn=%lld", __func__, start_lpn, nr_lba, end_lpn);
	if ((end_lpn / nr_parts) >= spp->tt_pgs) {
		NVMEV_ERROR("%s: lpn passed FTL range (start_lpn=%lld > tt_pgs=%ld)\n", __func__,
			    start_lpn, spp->tt_pgs);
		return false;
	}

	if (LBA_TO_BYTE(nr_lba) <= (KB(4) * nr_parts)) {
		srd.stime += spp->fw_4kb_rd_lat;
	} else {
		srd.stime += spp->fw_rd_lat;
	}

	for (i = 0; (i < nr_parts) && (start_lpn <= end_lpn); i++, start_lpn++) {
		conv_ftl = &conv_ftls[start_lpn % nr_parts];
		xfer_size = 0;
		prev_ppa = get_maptbl_ent(conv_ftl, start_lpn / nr_parts);

		/* normal IO read path */
		for (lpn = start_lpn; lpn <= end_lpn; lpn += nr_parts) {
			uint64_t local_lpn;
			struct ppa cur_ppa;

			local_lpn = lpn / nr_parts;
			cur_ppa = get_maptbl_ent(conv_ftl, local_lpn);
			if (!mapped_ppa(&cur_ppa) || !valid_ppa(conv_ftl, &cur_ppa)) {
				NVMEV_DEBUG_VERBOSE("lpn 0x%llx not mapped to valid ppa\n", local_lpn);
				NVMEV_DEBUG_VERBOSE("Invalid ppa,ch:%d,lun:%d,blk:%d,pl:%d,pg:%d\n",
					    cur_ppa.g.ch, cur_ppa.g.lun, cur_ppa.g.blk,
					    cur_ppa.g.pl, cur_ppa.g.pg);
				continue;
			}

			// aggregate read io in same flash page
			if (mapped_ppa(&prev_ppa) &&
			    is_same_flash_page(conv_ftl, cur_ppa, prev_ppa)) {
				xfer_size += spp->pgsz;
				continue;
			}

			if (xfer_size > 0) {
				srd.xfer_size = xfer_size;
				srd.ppa = &prev_ppa;
				nsecs_completed = ssd_advance_nand(conv_ftl->ssd, &srd);
				nsecs_latest = max(nsecs_completed, nsecs_latest);
			}

			xfer_size = spp->pgsz;
			prev_ppa = cur_ppa;
		}

		// issue remaining io
		if (xfer_size > 0) {
			srd.xfer_size = xfer_size;
			srd.ppa = &prev_ppa;
			nsecs_completed = ssd_advance_nand(conv_ftl->ssd, &srd);
			nsecs_latest = max(nsecs_completed, nsecs_latest);
		}
	}

	ret->nsecs_target = nsecs_latest;
	ret->status = NVME_SC_SUCCESS;
	return true;
}

static inline uint16_t nvme_make_pid(struct nvmev_ns *ns, uint16_t rg, uint16_t ph)//update~
{
        uint16_t rgif = ns->endgrps.fdp.rgif;

        if (rgif == 0)
                return ph;

        return (rg << (16 - rgif) | ph);
}       //~update

static inline bool nvme_ph_valid(struct nvmev_ns *ns, uint16_t ph)     //update~
{
        return ph < ns->fdp_ns.nphs;
}       //~update

static inline bool nvme_rg_valid(struct nvmev_ns *ns, uint16_t rg) //update~
{
        return rg < ns->endgrps.fdp.nrg;
}

static inline uint16_t nvme_pid2ph(struct nvmev_ns *ns, uint16_t pid)   //update~
{
        uint16_t rgif = ns->endgrps.fdp.rgif;

        if (rgif == 0)
                return pid;

        return pid & ((1 << (15 - rgif))- 1);
}       //~update

static inline uint16_t nvme_pid2rg(struct nvmev_ns *ns, uint16_t pid)   //update~
{
        uint16_t rgif = ns->endgrps.fdp.rgif;

        if (rgif == 0)
                return 0;

        return pid >> (16 - rgif);
}       //~update 

static inline bool nvme_parse_pid(struct nvmev_ns *ns, uint16_t pid, uint16_t *ph, uint16_t *rg)        //update~
{
        *ph = pid & 0x3FF;//nvme_pid2ph(ns, pid);
        *rg = (pid >> 10) & 0x3F;//nvme_pid2rg(ns, pid);

        return nvme_ph_valid(ns, *ph) && nvme_rg_valid(ns, *rg);
}       //~update

#  define __MAXUINT__(T) ((T) -1)
#  define UINT64_MAX __MAXUINT__(uint64_t)

static inline void nvme_fdp_stat_inc(uint64_t *a, uint64_t b)                                   //update~
{
    uint64_t ret = *a + b;
    *a = ret < *a ? UINT64_MAX : ret;
}

static inline int log_event(struct NvmeRuHandle *ruh, uint8_t event_type)                              //update~
{
    return (ruh->event_filter >> nvme_fdp_evf_shifts[event_type]) & 0x1;
}    //~update

static struct NvmeFdpEvent *nvme_fdp_alloc_event(struct nvmev_ns *ns, struct NvmeFdpEventBuffer *ebuf)//update~
{
        struct NvmeFdpEvent *ret = NULL;
        bool is_full = ebuf->next == ebuf->start && ebuf->nelems;

        ret = &ebuf->events[ebuf->next++]; // allocation
        if (ebuf->next == NVME_FDP_MAX_EVENTS)
                ebuf->next = 0;
        if (is_full)
                ebuf->start = ebuf->next;
        else
                ebuf->nelems++;

        memset(ret, 0, sizeof(struct NvmeFdpEvent)); // fill the 'ret' with 0
        ret->timestamp = nvmev_vdev->time_stamp; //update

        return ret;
}

static bool nvme_update_ruh(struct nvmev_ns *ns, uint16_t pid)
{
	struct NvmeRuHandle *ruh;
        const uint8_t lba_index = NVME_ID_NS_FLBAS_INDEX(0);
        const uint8_t data_shift = 9;
        struct NvmeReclaimUnit *ru;
        struct NvmeFdpEvent *e = NULL;
        uint64_t data_size;
        uint16_t ph, rg, ruhid;

	if (!nvme_parse_pid(ns, pid, &ph, &rg))
                return false;

	/* A stage that changes PHNDL to RUH */
        ruhid = ns->fdp_ns.phs[ph];
        ruh = &ns->endgrps.fdp.ruhs[ruhid];
        ru = &ruh->rus[rg];

        data_size = (uint64_t)ru->ruamw << data_shift;

        if (ru->ruamw)
        {
        // Logging only when the device updates an RUH implicitly,
        // Not logging when the host updates an RUH explicitly by i/o mgmt cmd.
                if (log_event(ruh, FDP_EVT_RU_NOT_FULLY_WRITTEN))
                {
                        e = nvme_fdp_alloc_event(ns, &ns->endgrps.fdp.host_events);
                        e->type = FDP_EVT_RU_NOT_FULLY_WRITTEN;
                        e->flags = FDPEF_PIV | FDPEF_NSIDV | FDPEF_LV;
                        e->pid = cpu_to_le16(pid);
                        e->nsid = cpu_to_le32(ns->id);
                        e->rgid = cpu_to_le16(rg);
                        e->ruhid = cpu_to_le16(ruhid);
                }

                nvme_fdp_stat_inc(&ns->endgrps.fdp.mbmw, data_size);
        }

        ru->ruamw = ruh->ruamw; // Reset
	return true;
}

static void nvme_do_write_fdp(struct nvmev_ns *ns, struct nvmev_request *req, uint64_t nlb) {
    struct nvme_command *cmd = req->cmd;
    const uint8_t lba_index = NVME_ID_NS_FLBAS_INDEX(0);
    const uint8_t data_shift = 9;
    uint64_t data_size = (uint64_t)nlb << data_shift;

    uint32_t dw12 = le32_to_cpu(cmd->fdp_cmd.cdw12);
    uint8_t dtype = (dw12 >> 20) & 0xf;
    uint16_t pid = le16_to_cpu(cmd->rw.dspec);
    uint16_t ph, rg, ruhid;
    struct NvmeReclaimUnit *ru;

    
    if (dtype != NVME_DIRECTIVE_DATA_PLACEMENT || !nvme_parse_pid(ns, pid, &ph, &rg))
    {
        ph = 0;
        rg = 0;
    }
    
    ruhid = ns->fdp_ns.phs[ph];
    ru = &ns->endgrps.fdp.ruhs[ruhid].rus[rg];
    nvme_fdp_stat_inc(&ns->endgrps.fdp.hbmw, data_size);
    nvme_fdp_stat_inc(&ns->endgrps.fdp.mbmw, data_size);
    
    while (nlb) {
        if (nlb < ru->ruamw) {
//	    printk("works here !!!\r\n");
            ru->ruamw -= nlb;
            break;
        }

        nlb -= ru->ruamw;
        nvme_update_ruh(ns, pid);
    }
    

   // printk("ru->ruamw : %lld, nlb : %lld\r\n",ru->ruamw, nlb);
   // printk("ruhid : %d rg : %d\n",ruhid, rg);
}

static bool conv_write(struct nvmev_ns *ns, struct nvmev_request *req, struct nvmev_result *ret)
{
	struct conv_ftl *conv_ftls = (struct conv_ftl *)ns->ftls;
	struct conv_ftl *conv_ftl = &conv_ftls[0];

	/* wbuf and spp are shared by all instances */
	struct ssdparams *spp = &conv_ftl->ssd->sp;
	struct buffer *wbuf = conv_ftl->ssd->write_buffer;

	struct nvme_command *cmd = req->cmd;
	uint64_t lba = cmd->rw.slba;
	uint64_t nr_lba = (cmd->rw.length + 1);
	uint64_t start_lpn = lba / spp->secs_per_pg;
	uint64_t end_lpn = (lba + nr_lba - 1) / spp->secs_per_pg;

	uint64_t lpn;
	uint32_t nr_parts = ns->nr_parts;

	uint64_t nsecs_latest;
	uint64_t nsecs_xfer_completed;
	uint32_t allocated_buf_size;

	struct nand_cmd swr = {
		.type = USER_IO,
		.cmd = NAND_WRITE,
		.interleave_pci_dma = false,
		.xfer_size = spp->pgsz * spp->pgs_per_oneshotpg,
	};
	NVMEV_DEBUG_VERBOSE("%s: start_lpn=%lld, len=%lld, end_lpn=%lld", __func__, start_lpn, nr_lba, end_lpn);
	if ((end_lpn / nr_parts) >= spp->tt_pgs) {
		NVMEV_ERROR("%s: lpn passed FTL range (start_lpn=%lld > tt_pgs=%ld)\n",
				__func__, start_lpn, spp->tt_pgs);
		return false;
	}

	if (ns->endgrps.fdp.enabled == true) { //update~
                nvme_do_write_fdp(ns, req, nr_lba);
        }

	bool fdp_enabled = ns->endgrps.fdp.enabled;
        uint64_t nlb = nr_lba;
        const uint8_t lba_index = NVME_ID_NS_FLBAS_INDEX(0);
        const uint8_t data_shift = 9;
        uint64_t data_size = (uint64_t)nlb << data_shift;
	
	uint16_t rgif = ns->endgrps.fdp.rgif;
        uint32_t dw12 = le32_to_cpu(cmd->fdp_cmd.cdw12);
        uint8_t dtype = (dw12 >> 20) & 0xf;
        uint16_t pid = le16_to_cpu(cmd->rw.dspec);	//Placement Identifier
    	uint16_t rgid = pid >> (16 - rgif);		//Reclaim Group ID
       	uint16_t ph = pid & ((1 << (15 - rgif)) - 1);	//Placement Handle
        uint16_t ruhid;					//Reclaim Unit Handler Identifier
							// == Placement Identifier

        int r = 0;
	printk("ph = %d, rgid = %d\n", ph, rgid);

	if (dtype != NVME_DIRECTIVE_DATA_PLACEMENT) {
                ph = 0;
                rgid = 0; // TODO: consider striping later
        }

	ruhid = ns->fdp_ns.phs[ph];	//phs[i] = i
        if (end_lpn >= spp->tt_pgs) {
                NVMEV_DEBUG_VERBOSE("%s: start_lpn=%lld, tt_pgs=%d\r\n", __func__, start_lpn, ssd->sp.tt_pgs);
        }
	if (fdp_enabled) {      //update~
                // perform GC here until !should_fdp_gc(ssd, rgid) 
                while (should_fdp_gc_high(conv_ftl, rgid)) {
#ifdef FDP_DEBUG
                        NVMEV_DEBUG_VERBOSE("do_fdp_gc() called in high\n");
#endif
                        spp->tt_valid_pgs -= spp->pgs_per_ru;
                        r = do_fdp_gc(conv_ftl, rgid, true, req);
#ifdef DEVICE_UTIL_DEBUG
#endif
                        if (r == -1)
                                break;
                }

        }                                       //~update
        else {
                // perform GC here until !should_gc(ssd) 
                while (should_gc_high(conv_ftl)) {
                        r = do_gc(conv_ftl, true);
                        if (r == -1)
                                break;
                }
        }

	allocated_buf_size = buffer_allocate(wbuf, LBA_TO_BYTE(nr_lba));
	if (allocated_buf_size < LBA_TO_BYTE(nr_lba))
		return false;

	nsecs_latest =
		ssd_advance_write_buffer(conv_ftl->ssd, req->nsecs_start, LBA_TO_BYTE(nr_lba));
	nsecs_xfer_completed = nsecs_latest;

	swr.stime = nsecs_latest;

	for (lpn = start_lpn; lpn <= end_lpn; lpn++) {
		uint64_t local_lpn;
		uint64_t nsecs_completed = 0;
		struct ppa ppa;

		//conv_ftl = &conv_ftls[lpn % nr_parts];
		local_lpn = lpn / nr_parts;
		ppa = get_maptbl_ent(
			conv_ftl, local_lpn); // Check whether the given LPN has been written before
		if (mapped_ppa(&ppa)) {
			// update old page information first 
			mark_page_invalid(conv_ftl, &ppa);
			set_rmap_ent(conv_ftl, INVALID_LPN, &ppa);
			NVMEV_DEBUG("%s: %lld is invalid, ", __func__, ppa2pgidx(conv_ftl, &ppa));
		}

		// new write 
		//ppa = get_new_page(conv_ftl, USER_IO);
		ppa = (fdp_enabled ? fdp_get_new_page(conv_ftl, USER_IO, rgid, ruhid) : get_new_page(conv_ftl, USER_IO));
		printk("fdp_get_new_page \nch : %d, lun : %d, pg : %d, blk : %d, pl : %d\r\n", ppa.g.ch, ppa.g.lun, ppa.g.pg, ppa.g.blk, ppa.g.pl);
		// update maptbl 
		set_maptbl_ent(conv_ftl, local_lpn, &ppa);
		NVMEV_DEBUG("%s: got new ppa %lld, ", __func__, ppa2pgidx(conv_ftl, &ppa));
		// update rmap 
		set_rmap_ent(conv_ftl, local_lpn, &ppa);
		mark_page_valid(conv_ftl, &ppa);
		// need to advance the write pointer here 
		//advance_write_pointer(conv_ftl, USER_IO);
		if (fdp_enabled)  {
                        advance_fdp_write_pointer(conv_ftl, USER_IO, rgid, ruhid);
                }
                else {
                        advance_write_pointer(conv_ftl, USER_IO);
                }

		// Aggregate write io in flash page 
		if (last_pg_in_wordline(conv_ftl, &ppa)) {
			swr.ppa = &ppa;

			nsecs_completed = ssd_advance_nand(conv_ftl->ssd, &swr);
			nsecs_latest = max(nsecs_completed, nsecs_latest);

			schedule_internal_operation(req->sq_id, nsecs_completed, wbuf,
						    spp->pgs_per_oneshotpg * spp->pgsz);
		}

		consume_write_credit(conv_ftl);
		check_and_refill_write_credit(conv_ftl);
	}

	if ((cmd->rw.control & NVME_RW_FUA) || (spp->write_early_completion == 0)) {
		// Wait all flash operations 
		ret->nsecs_target = nsecs_latest;
	} else {
		 //Early completion 
		ret->nsecs_target = nsecs_xfer_completed;
	}
	
	ret->status = NVME_SC_SUCCESS;
	return true;
}

#define prp_address_offset(prp, offset) \
        (page_address(pfn_to_page(prp >> PAGE_SHIFT) + offset) + (prp & ~PAGE_MASK))
#define prp_address(prp) prp_address_offset(prp, 0)

#define MIN(a, b) ((a) < (b) ? (a) : (b))

#define MAX(a, b) ((a) > (b) ? (a) : (b))

static void nvme_io_mgmt_recv_ruhs(struct nvmev_ns *ns, struct nvmev_request *req, struct nvmev_result *ret, size_t len)
{
	struct nvme_command *cmd = req->cmd;
	struct NvmeEnduranceGroup *endgrp;
    	struct NvmeRuhStatus *hdr;
    	struct NvmeRuhStatusDescr *ruhsd;

	unsigned int nruhsd;
    	uint16_t rg, ph, *ruhid;
    	size_t trans_len;
    	uint8_t *buf = NULL;  // A buffer to be transmitted to host
        uint64_t prp1 = le64_to_cpu(cmd->fdp_cmd.dptr.prp1); //update
        uint64_t prp2 = le64_to_cpu(cmd->fdp_cmd.dptr.prp2); //update
	void *page;	
	page = prp_address(prp1);
	endgrp = &ns->endgrps;
	nruhsd = ns->fdp_ns.nphs * endgrp->fdp.nrg;
	trans_len = sizeof(struct NvmeRuhStatus) + nruhsd * sizeof(struct NvmeRuhStatusDescr);
	buf = kzalloc(sizeof(size_t), GFP_KERNEL);
	trans_len = MIN(trans_len, len);
	hdr = (struct NvmeRuhStatus *)buf; // Start Address of RUHS
    	ruhsd = (struct NvmeRuhStatusDescr *)(buf + sizeof(struct NvmeRuhStatus)); // Start Address of RUHSD
	hdr->nruhsd = cpu_to_le16(nruhsd);
	ruhid = ns->fdp_ns.phs;
	for (ph = 0; ph < ns->fdp_ns.nphs; ph++, *ruhid++) {
            struct NvmeRuHandle *ruh = &endgrp->fdp.ruhs[*ruhid];
        for (rg = 0; rg < endgrp->fdp.nrg; rg++, ruhsd++) {
            uint16_t pid = nvme_make_pid(ns, rg, ph);
            ruhsd->pid = cpu_to_le16(pid);
            ruhsd->ruhid = *ruhid;
            ruhsd->earutr = 0;
            ruhsd->ruamw = cpu_to_le64(ruh->rus[rg].ruamw);
        }
    }
   __memcpy(page, buf, trans_len); 	
}

static void conv_io_mgmt_recv(struct nvmev_ns *ns, struct nvmev_request *req, struct nvmev_result *ret)
{
    struct nvme_command *cmd = req->cmd;
    uint32_t cdw10 = le32_to_cpu(cmd->fdp_cmd.cdw10);
    uint32_t numd = le32_to_cpu(cmd->fdp_cmd.cdw11);
    uint8_t mo = (cdw10 & 0xff); // Management operation
    size_t len = (numd + 1) << 2; // unit: byte
    
    //printk("mo : 0x%x\r\n",mo);
    switch (mo) {
    case NVME_IOMR_MO_NOP:
        break;
    case NVME_IOMR_MO_RUH_STATUS:
        nvme_io_mgmt_recv_ruhs(ns, req, ret, len);
	break;
    default:
        break;
    };
}

static void conv_flush(struct nvmev_ns *ns, struct nvmev_request *req, struct nvmev_result *ret)
{
	uint64_t start, latest;
	uint32_t i;
	struct conv_ftl *conv_ftls = (struct conv_ftl *)ns->ftls;

	start = local_clock();
	latest = start;
	for (i = 0; i < ns->nr_parts; i++) {
		latest = max(latest, ssd_next_idle_time(conv_ftls[i].ssd));
	}

	NVMEV_DEBUG_VERBOSE("%s: latency=%llu\n", __func__, latest - start);

	ret->status = NVME_SC_SUCCESS;
	ret->nsecs_target = latest;
	return;
}

bool conv_proc_nvme_io_cmd(struct nvmev_ns *ns, struct nvmev_request *req, struct nvmev_result *ret)
{
	struct nvme_command *cmd = req->cmd;
	NVMEV_ASSERT(ns->csi == NVME_CSI_NVM);

	switch (cmd->common.opcode) {
	case (nvme_cmd_write):
		if (!conv_write(ns, req, ret))
			return false;
		break;
	case nvme_cmd_read:
		if (!conv_read(ns, req, ret))
			return false;
		break;
	case nvme_cmd_flush:
		conv_flush(ns, req, ret);
		break;
	case nvme_cmd_io_mgmt_send:	//update to do ~
		break;
	case nvme_cmd_io_mgmt_recv:
		conv_io_mgmt_recv(ns, req, ret);
		break;			//~ udpate to do
	default:
		NVMEV_ERROR("%s: command not implemented: %s (0x%x)\n", __func__,
				nvme_opcode_string(cmd->common.opcode), cmd->common.opcode);
		break;
	}

	return true;
}
