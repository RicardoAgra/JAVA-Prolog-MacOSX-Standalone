/* Copyright(C) 1999, Swedish Institute of Computer Science */

#include "fd.h"
#include "dvars.h"

/*
   '$fd_relation'(+State0, -State, -Actions) :-
   State0 is f(X,XMut,Y,YMut,Xu,Yu,XY,Opt) where
   Xu is the previous X domain,
   Yu is the previous Y domain,
   XY is the extension repr. as Xset-Yset pairs (unique X)
   (Opt & 0x1) iff bound-consistent, otherwise arc-consistent
   (Opt & 0x2) iff Y sets are all disjoint,
   (Opt & 0x4) iff Y sets form increasing, disjoint intervals
   Actions is a list of prunings etc.
*/
struct relation_data {
  void (SPCDECL *destructor)(void *);
  void (SPCDECL *daemon)(Wam,void *,SP_globref,TAGGED); /* (wam,handle,attr_ref,global) */
  SPEnv *spenv;

  SP_integer stamp;
  SP_integer first;			/* head of (-1)-terminated list of queued tuples */
  SP_integer *next;			/* next[i]==(-2) iff not in the queue */
  struct dvar *dvbase;
  SP_globref refbase;		/* {XMut, X, UXMut, YMut, Y, UYMut}ntuples, Y{xy_n} */
  int ntuples;			/* #tuples */
  int xy_n;			/* #values in X->Y extension */
  int xy_r;			/* #X intervals in X->Y extension */
  int opt;
  struct mapentry *map;
};

struct mapentry {
  TAGGED min;
  TAGGED max;
  TAGGED ymin;
  TAGGED ymax;
  SP_globref value;
};


static int cmp_map(Wam wam, struct mapentry *t1, struct mapentry *t2)
{
  (void)wam;
  return FDCMP(t1->min,t2->min); /* 20120516 */
}

#define QType struct mapentry
#define QCmp  cmp_map
#define QSort qsort_map
#include "qsort.ic"

static void SPCDECL relation_destructor(void *pdata_v)
{
  struct relation_data *pdata = (struct relation_data *)pdata_v;
  FD_SETUP_SPENV(pdata->spenv)

  SP_free_globrefs(pdata->refbase,pdata->xy_n+6*pdata->ntuples);
  SP_free(pdata);
}


static TAGGED
relation_fdset(Wam wam, SP_globref attr_ref)
{
  TAGGED tmp = RefGlob(attr_ref);
  TAGGED *h, min, max, t;

  DerefAttribute(tmp,tmp);	/* get dom/4 term */
  tmp = DomainSet(tmp);
				/* protect from smashing */
  t = CTagToCar(tmp);
  min = RangeMin(t);
  max = RangeMax(t);
  t = CTagToCdr(tmp);
  RequireHeap1(4,t,EVAL_ARITY);
  h = w->global_top;
  w->global_top = h+4;
  h[0] = min;
  h[1] = max;
  h[2] = MakeList(h);
  h[3] = t;
  return MakeList(h+2);
}

static void
relation_scan_dom_interval(Wam wam,
			   struct relation_data *pdata,
			   TAGGED min, TAGGED max, /* Invariant: this \subseteq the set of X values */
			   TAGGED miny, TAGGED maxy,
			   SP_BOOL nodeltay,
			   TAGGED *punsafex,
			   TAGGED *punsafey)
{
  TAGGED unsafex, mins, maxs;
  int ix = 0;
  int ixend = pdata->xy_r;
  
  unsafex = fd_interval(wam, min,max);
  mins = Sup;
  maxs = Inf;

  /* scan */
  while (ix<ixend && FDle(pdata->map[ix].min,max)) {
    struct mapentry *mapix = &pdata->map[ix];

    if (FDgt(min,mapix->max)) {
      /* dichotomic search for next hit */
      int mid;
      int sup = ixend;
      while (ix<sup) {
	mid = (ix+sup)>>1;
	if (FDgt(min,pdata->map[mid].max))
	  ix = mid+1;
	else
	  sup = mid;
      }
    } else {
      if (nodeltay)
	goto hity;
      else if (mapix->ymin==mapix->ymax) {
	if (InInterval(mapix->ymin,miny,maxy)) {
	  goto hit;
	}
      } else {
	switch (fd_compare_interval(RefGlob(mapix->value),miny,maxy)) {
	case FDI_DISJOINT:
	  break;
	default:
	hit:
	  unsafex = fd_subtract_interval(wam, unsafex,mapix->min,mapix->max);
	hity:
	  if (FDgt(mins,mapix->ymin))
	    mins = mapix->ymin;
	  if (FDlt(maxs,mapix->ymax))
	    maxs = mapix->ymax;
	  if (nodeltay && FDle(mins,miny) && FDge(maxs,maxy))
	    goto rety;
	}
      }
      ix++;
      if (ix==ixend)
	break;
      min = pdata->map[ix].min;
    }
  }
  if (!nodeltay)
    *punsafex = unsafex;
 rety:
  if (mins==Sup)
    *punsafey = fd_interval(wam, Inf,Sup);
  else
    *punsafey = fd_complement(wam, fd_interval(wam, mins,maxs));
}

static void
relation_scan_dom(Wam wam,
		  struct relation_data *pdata,
		  TAGGED domainx, /* Invariant: this \subseteq the set of X values */
		  TAGGED domainy,
		  SP_BOOL nodeltay,
		  TAGGED *punsafex,
		  TAGGED *punsafey)
{
  TAGGED unsafex, unsafey, min, max, domainx_rest;
  int ix = 0;
  int ixend = pdata->xy_r;
  
  unsafex = domainx;
  unsafey = domainy;
  min = fd_min(domainx);
  max = fd_max(domainx);
  domainx_rest = fd_interval(wam, Inf,Sup);

  /* scan */
  while (ix<ixend && FDle(pdata->map[ix].min,max)) {
    struct mapentry *mapix = &pdata->map[ix];

    if (FDgt(min,mapix->max)) {
      /* dichotomic search for next hit */
      int mid;
      int sup = ixend;
      while (ix<sup) {
	mid = (ix+sup)>>1;
	if (FDgt(min,pdata->map[mid].max))
	  ix = mid+1;
	else
	  sup = mid;
      }
    } else {
      if (nodeltay)
	goto hity;
      else if (mapix->ymin==mapix->ymax) {
	if (fd_member(mapix->ymin,domainy)) {
	  unsafex = fd_subtract_interval(wam, unsafex,mapix->min,mapix->max);
	  unsafey = fd_subtract_interval(wam, unsafey,mapix->ymin,mapix->ymax);
	}
      } else {
	switch (fd_compare(domainy,RefGlob(mapix->value))) {
	case FDI_DISJOINT:
	  break;
	default:
	  unsafex = fd_subtract_interval(wam, unsafex,mapix->min,mapix->max);
	hity:
	  unsafey = fd_subtract(wam, unsafey,RefGlob(mapix->value));
	  if (nodeltay && unsafey==EmptySet)
	    goto rety;
	}
      }
      ix++;
      if (ix==ixend)
	break;
      RangeMin(CTagToCar(domainx_rest)) = pdata->map[ix].min;
      min = fd_intersection_min(domainx,domainx_rest);
    }
  }
  if (!nodeltay)
    *punsafex = unsafex;
 rety:
  *punsafey = unsafey;
}

static void
relation_scan_dom_symm(Wam wam,
		       struct relation_data *pdata,
		       TAGGED domainx, /* Invariant: this \subseteq the set of X values */
		       TAGGED domainy,
		       SP_BOOL nodeltay,
		       TAGGED *punsafex,
		       TAGGED *punsafey)
{
  TAGGED unsafex, unsafey, min, max, ymin, ymax, domainx_rest, domainy_rest;
  int ix = 0;
  int ixend = pdata->xy_r;
  
  unsafex = domainx;
  unsafey = domainy;
  min = fd_min(domainx);
  max = fd_max(domainx);
  domainx_rest = fd_interval(wam, Inf,Sup);
  ymin = fd_min(domainy);
  ymax = fd_max(domainy);
  domainy_rest = fd_interval(wam, Inf,Sup);

  /* scan */
  while (ix<ixend && FDle(pdata->map[ix].min,max) && FDle(pdata->map[ix].ymin,ymax)) {
    struct mapentry *mapix = &pdata->map[ix];

    if (FDgt(min,mapix->max) || FDgt(ymin,mapix->ymax)) {
      /* dichotomic search for next hit */
      int mid;
      int sup = ixend;
      while (ix<sup) {
	mid = (ix+sup)>>1;
	if (FDgt(min,pdata->map[mid].max) || FDgt(ymin,pdata->map[mid].ymax))
	  ix = mid+1;
	else
	  sup = mid;
      }
    } else {
      if (fd_compare_interval(domainx,mapix->min,mapix->max)==FDI_DISJOINT)
	;
      else if (nodeltay)
	goto hity;
      else if (mapix->ymin==mapix->ymax) {
	if (fd_member(mapix->ymin,domainy)) {
	  unsafex = fd_subtract_interval(wam, unsafex,mapix->min,mapix->max);
	  unsafey = fd_subtract_interval(wam, unsafey,mapix->ymin,mapix->ymax);
	}
      } else {
	switch (fd_compare_interval(domainy,mapix->ymin,mapix->ymax)) {
	case FDI_DISJOINT:
	  break;
	default:
	  unsafex = fd_subtract_interval(wam, unsafex,mapix->min,mapix->max);
	hity:
	  unsafey = fd_subtract_interval(wam, unsafey,mapix->ymin,mapix->ymax);
	  if (nodeltay && unsafey==EmptySet)
	    goto rety;
	}
      }
      ix++;
      if (ix==ixend)
	break;
      RangeMin(CTagToCar(domainx_rest)) = pdata->map[ix].min;
      min = fd_intersection_min(domainx,domainx_rest);
      RangeMin(CTagToCar(domainy_rest)) = pdata->map[ix].ymin;
      ymin = fd_intersection_min(domainy,domainy_rest);
    }
  }
  if (!nodeltay)
    *punsafex = unsafex;
 rety:
  *punsafey = unsafey;
}


static void
relation_scan_delta(Wam wam,
		    struct relation_data *pdata,
		    TAGGED deltax, /* Invariant: this \subseteq the set of X values */
		    TAGGED domainx,
		    TAGGED *punsafey)
{
  TAGGED unsafey, min, max, domainx_rest;
  int ix = 0;
  int ixend = pdata->xy_r;
  
  unsafey = EmptySet;
  if (deltax==EmptySet)
    goto ret;
  min = fd_min(deltax);
  max = fd_max(deltax);
  domainx_rest = fd_interval(wam, Inf,Sup);

  /* scan */
  while (ix<ixend && FDle(pdata->map[ix].min,max)) {
    struct mapentry *mapix = &pdata->map[ix];

    if (FDgt(min,mapix->max)) {
      /* dichotomic search for next hit */
      int mid;
      int sup = ixend;
      while (ix<sup) {
	mid = (ix+sup)>>1;
	if (FDgt(min,pdata->map[mid].max))
	  ix = mid+1;
	else
	  sup = mid;
      }
    } else {
      switch (fd_compare_interval(domainx,mapix->min,mapix->max)) {
      case FDI_DISJOINT:
	unsafey = fd_union(wam, unsafey,RefGlob(mapix->value));
      }
      ix++;
      if (ix==ixend)
	break;
      RangeMin(CTagToCar(domainx_rest)) = pdata->map[ix].min;
      min = fd_intersection_min(deltax,domainx_rest);
    }
  }
 ret:
  *punsafey = unsafey;
}

static void
relation_scan_delta_symm(Wam wam,
			 struct relation_data *pdata,
			 TAGGED deltay, /* Invariant: this \subseteq the set of Y values */
			 TAGGED domainy,
			 TAGGED *punsafex)
{
  TAGGED unsafex, ymin, ymax, domainy_rest;
  int ix = 0;
  int ixend = pdata->xy_r;
  
  unsafex = EmptySet;
  if (deltay==EmptySet)
    goto ret;
  ymin = fd_min(deltay);
  ymax = fd_max(deltay);
  domainy_rest = fd_interval(wam, Inf,Sup);

  /* scan */
  while (ix<ixend && FDle(pdata->map[ix].ymin,ymax)) {
    struct mapentry *mapix = &pdata->map[ix];

    if (FDgt(ymin,mapix->ymax)) {
      /* dichotomic search for next hit */
      int mid;
      int sup = ixend;
      while (ix<sup) {
	mid = (ix+sup)>>1;
	if (FDgt(ymin,pdata->map[mid].ymax))
	  ix = mid+1;
	else
	  sup = mid;
      }
    } else {
      switch (fd_compare_interval(domainy,mapix->ymin,mapix->ymax)) {
      case FDI_DISJOINT:
	unsafex = fd_union_interval(wam, unsafex,mapix->min,mapix->max);
      }
      ix++;
      if (ix==ixend)
	break;
      RangeMin(CTagToCar(domainy_rest)) = pdata->map[ix].ymin;
      ymin = fd_intersection_min(deltay,domainy_rest);
    }
  }
 ret:
  *punsafex = unsafex;
}


static void SPCDECL 
relation_daemon(Wam wam,
		void *vdata,
		SP_globref attr_ref,
		TAGGED global)
{
  struct relation_data *pdata = (struct relation_data *)vdata;
  SP_globref refoffset;
  TAGGED tstate;
  int ar, argno, state_stamp;
  SP_integer f, n;

  argno = (int)((attr_ref - pdata->refbase)/6);
  tstate = RefMutable(CTagToArg(global,1));
  ar = Arity(TagToHeadfunctor(tstate));
  state_stamp = GetSmall_int(CTagToArg(tstate,ar));
  refoffset = pdata->refbase + 6*argno;
  if (fd_singleton(RefMutable(RefGlob(refoffset+2))) ||
      fd_singleton(RefMutable(RefGlob(refoffset+5))))
    return;			/* tuple already entailed */
  if (pdata->stamp!=state_stamp) { /* non-incremental */
    for (f = pdata->first; f != -1; f = n) {
      n = pdata->next[f];
      pdata->next[f] = -2;
    }
    pdata->first = -1;
    pdata->stamp = state_stamp;
  }
  if (pdata->first == -1) {
    SP_BOOL buried;
    (void)fd_daemon_copy_state(wam, &global,&buried);
    pdata->stamp++;
    fd_enqueue_global(wam, global, 0x7/* DOM, append*/);
  }
  if (pdata->next[argno] == -2) {
    pdata->next[argno] = pdata->first;
    pdata->first = argno;
  }
}

void SPCDECL
prolog_fd_relation(Wam wam,
		   SP_term_ref State0,
		   SP_term_ref State,
		   SP_term_ref Actions)
{
  int ent = -1;			/* disentailed */
  int current;
  int opt;
  SP_BOOL committed, post;
  SP_BOOL idempotent;
  TAGGED handle;
  char *ptr;
  struct relation_data *pdata;
  DECL_UPDATE_MUTABLE;
  
/* X(0) = RefTerm(State0); */
  (void)State0;
  dvar_export_start(wam);
  RefTerm(State) = fd_static_output_state(wam,&handle,&committed);

  if (!IsVar(handle)) {		/* got [Flag | '$free'(Ptr)] */
    pdata = Pdata(struct relation_data,handle);
    post = FALSE;
  } else {
    int xy_n, xy_r, ntuples;
    SP_integer total_size;
    TAGGED xy, t1;
    int j;
    SP_globref refoffset;
    
    DerefArg(xy,X(0),1);	/* get XY */
    xy_n = fd_list_length(xy);
    xy_r = 0;
    t1 = xy;
    while (TagIsLST(t1)) {
      TAGGED t2;
      DerefCar(t2,t1);
      DerefArg(t2,t2,1);
      DerefCdr(t1,t1);
      xy_r += fd_list_length(t2);
    }
    DerefArg(t1,X(0),3);	/* get Tuples */
    ntuples = fd_list_length(t1);
    total_size = xy_r*sizeof(struct mapentry) +
      ntuples*sizeof(SP_integer) +
      ntuples*2*sizeof(struct dvar);
    pdata = Palloc(struct relation_data, total_size, handle);
    /* store header data */
    pdata->destructor = relation_destructor;
    pdata->daemon = relation_daemon;
    FD_STORE_SPENV(pdata->spenv);
    pdata->refbase = SP_alloc_globrefs(xy_n+6*ntuples);
    pdata->ntuples = ntuples;
    pdata->xy_n = xy_n;
    pdata->xy_r = xy_r;
    ptr = (char *)(pdata+1);
    pdata->map = (struct mapentry *)ptr; ptr += xy_r*sizeof(struct mapentry);
    pdata->next = (SP_integer *)ptr; ptr += ntuples*sizeof(SP_integer);
    pdata->dvbase = (struct dvar *)ptr; ptr += ntuples*2*sizeof(struct dvar);
    SP_ASSERT(ptr == (char *)(pdata+1)+total_size);
    pdata->stamp = 0;
    refoffset = pdata->refbase;
    DerefArg(xy,X(0),1);	/* get XY */
    DerefArg(t1,X(0),3);	/* refresh Tuples */
    while (TagIsLST(t1)) {
      TAGGED t2, t3;
      DerefCar(t2,t1);
      DerefCdr(t1,t1);
      fd_get_var_and_attr(t2,refoffset); /* init X, XM */
      DerefArg(t3,t2,3);	/* init UXMut */
      RefGlob(refoffset+2) = t3;
      fd_get_var_and_attr(t2+WD(3),refoffset+3); /* init Y, YM */
      DerefArg(t3,t2,6);	/* init UYMut */
      RefGlob(refoffset+5) = t3;
      refoffset += 6;
    }
    pdata->first = ntuples-1;
    for (j=0; j<ntuples; j++)
      pdata->next[j] = j-1;
    DerefArg(t1,X(0),2);
    pdata->opt = (int)GetSmall(t1); /* get Opt */
    {
      int k=0;
      TAGGED ymin, ymax, list=xy;
      for (j=0; j<xy_n; j++) {
	TAGGED t2;
	DerefCar(t1,list);
	DerefCdr(list,list);
	DerefArg(t2,t1,2);	/* the "value" fdset */
	ymin = fd_min(t2);
	ymax = fd_max(t2);
	RefGlob(refoffset) = t2;
	DerefArg(t1,t1,1);	/* the "key" fdset */
	while (TagIsLST(t1)) {
	  t2 = CTagToCar(t1);
	  t1 = CTagToCdr(t1);
	  pdata->map[k].min = RangeMin(t2);
	  pdata->map[k].max = RangeMax(t2);
	  pdata->map[k].ymin = ymin;
	  pdata->map[k].ymax = ymax;
	  pdata->map[k].value = refoffset;
	  k++;
	}
	refoffset++;
      }
      qsort_map(wam, pdata->map,xy_r);
      k = 0x4;
      for (j=0; j<xy_r && k; j++) {
	struct mapentry *mapj0 = &pdata->map[j-1];
	struct mapentry *mapj = &pdata->map[j];
	if ((j>0 && FDge(mapj0->ymax,mapj->ymin)) || CTagToCdr(RefGlob(mapj->value))!=EmptySet)
	  k = 0;
      }
      pdata->opt |= k;
    }
    DerefArg(t1,X(0),4);	/* ensure entailment ctr is dereffed */
    CTagToArg(X(0),4) = t1;
    for (j=1; j<4; j++)
      CTagToArg(X(0),j) = atom_nil; /* [MC] 3.12: free for GC */
    post = TRUE;
  }
  idempotent = ((RefMutable(CTagToArg(X(1),3))&IStep(4))==0); /* STATUS: idempotent */
  opt  = pdata->opt;
  
  current = (int)pdata->first;
  while (current != -1) {
    TAGGED ux, uy, deltax, deltay, unsafex=EmptySet, unsafey=EmptySet;
    SP_globref refoffset = pdata->refbase + 6*current;
    struct dvar *dvoffset = pdata->dvbase + 2*current;

    dvar_init(dvoffset,   refoffset,   refoffset+1);
    dvar_init(dvoffset+1, refoffset+3, refoffset+4);
    ux = RefMutable(RefGlob(refoffset+2));	/* get UXMut */
    uy = RefMutable(RefGlob(refoffset+5));	/* get UYMut */
    deltax = fd_subtract(wam, ux,dvar_set(dvoffset));
    deltay = fd_subtract(wam, uy,dvar_set(dvoffset+1));

    if (opt & 0x4) {
      if (fd_size(deltax)+fd_size(deltay) < dvar_value_count(dvoffset)) {
	relation_scan_delta(wam, pdata,deltax,dvar_set(dvoffset),&unsafey);
	relation_scan_delta_symm(wam, pdata,deltay,dvar_set(dvoffset+1),&unsafex);
      } else {
	relation_scan_dom_symm(wam, pdata,dvar_set(dvoffset),dvar_set(dvoffset+1),(deltay==EmptySet),&unsafex,&unsafey);
      }
    } else if (opt & 0x2) {
      TAGGED deltax = fd_subtract(wam, ux,dvar_set(dvoffset));
      if (deltay==EmptySet && fd_size(deltax) < dvar_value_count(dvoffset)) {
	relation_scan_delta(wam, pdata,deltax,dvar_set(dvoffset),&unsafey);
      } else if (opt & 0x1) {
	goto scan_dom_int;
      } else {
	goto scan_dom;
      }
    } else if (opt & 0x1) {
    scan_dom_int:
      relation_scan_dom_interval(wam, pdata,dvar_min_t(dvoffset),dvar_max_t(dvoffset),dvar_min_t(dvoffset+1),dvar_max_t(dvoffset+1),(deltay==EmptySet),&unsafex,&unsafey);
    } else {
    scan_dom:
      relation_scan_dom(wam, pdata,dvar_set(dvoffset),dvar_set(dvoffset+1),(deltay==EmptySet),&unsafex,&unsafey);
    }
    if (unsafex!=EmptySet) {
      if (opt & 0x1) {
	ux = fd_subtract(wam, dvar_set(dvoffset),unsafex);
	if (dvar_fix_interval_t(dvoffset,fd_min(ux),fd_max(ux))<0)
	  goto ret;
      } else {
	if (dvar_prune_set(dvoffset,unsafex)<0)
	  goto ret;
      }
    }
    if (unsafey!=EmptySet) {
      if (opt & 0x1) {
	uy = fd_subtract(wam, dvar_set(dvoffset+1),unsafey);
	if (dvar_fix_interval_t(dvoffset+1,fd_min(uy),fd_max(uy))<0)
	  goto ret;
      } else {
	if (dvar_prune_set(dvoffset+1,unsafey)<0)
	  goto ret;
      }
    }
    dvar_pruning_done( dvoffset);
    dvar_pruning_done( dvoffset+1);
    if (!idempotent) {
      (dvoffset)->set = fd_localize(wam, dvar_set(dvoffset));
      (dvoffset+1)->set = fd_localize(wam, dvar_set(dvoffset+1));
    }
    if (!dvar_is_integer(dvoffset) && !dvar_is_integer(dvoffset+1)) {
      if (post) {
	dvar_attach_daemon(wam, dvoffset, pdata, X(1), fd.functor_dom);
	dvar_attach_daemon(wam, dvoffset+1, pdata, X(1), fd.functor_dom);
      }
    } else {
      CTagToArg(X(0),4) -= IStep(1); /* decrement entailent counter */
    }
    current = (int)pdata->next[current];
  }

  if (idempotent) {
    /* OK to GC */
    current = (int)pdata->first;
    while (current != -1) {
      SP_globref refoffset = pdata->refbase + 6*current;
      struct dvar *dvoffset = pdata->dvbase + 2*current;
      int next;
      TAGGED ux, uy;
    
      dvar_export(dvoffset);
      ux = relation_fdset(wam, refoffset);
      FD_UPDATE_MUTABLE(ux,RefGlob(refoffset+2)); /* put UXMut */
      dvar_export(dvoffset+1);
      uy = relation_fdset(wam, refoffset+3);
      FD_UPDATE_MUTABLE(uy,RefGlob(refoffset+5)); /* put UYMut */
      next = (int)pdata->next[current];
      pdata->next[current] = -2;
      current = next;
    }
  } else {
    /* OK to GC */
    current = (int)pdata->first;
    while (current != -1) {
      SP_globref refoffset = pdata->refbase + 6*current;
      struct dvar *dvoffset = pdata->dvbase + 2*current;
      TAGGED ux, uy;
    
      ux = dvar_set(dvoffset);
      ux = fd_globalize(wam, ux,0,3);
      FD_UPDATE_MUTABLE(ux,RefGlob(refoffset+2)); /* put UXMut */
      uy = dvar_set(dvoffset+1);
      uy = fd_globalize(wam, uy,0,3);
      FD_UPDATE_MUTABLE(uy,RefGlob(refoffset+5)); /* put UYMut */
      current = (int)pdata->next[current];
    }
    current = (int)pdata->first;
    while (current != -1) {
      struct dvar *dvoffset = pdata->dvbase + 2*current;
      int next;
    
      dvar_export(dvoffset);
      dvar_export(dvoffset+1);
      next = (int)pdata->next[current];
      pdata->next[current] = -2;
      current = next;
    }
  }
  pdata->first = -1;
  ent = Teqz(CTagToArg(X(0),4));
ret:
  if (ent==1)
    Pfree;
  dvar_export_done(wam, Actions, ent);
}

struct element_data {
  void (SPCDECL *destructor)(void *);
  void (SPCDECL *daemon)(Wam,void *,SP_globref,TAGGED); /* (wam,handle,attr_ref,global) */
  SPEnv *spenv;
  SP_globref refbase;
  int nrefs;
  Dvar dvar;
};

#define RefAttr(T) (pdata->refbase + 2*(T))
#define RefVar(T) (pdata->refbase + 2*(T) + 1)
#define DVAR(T) (pdata->dvar+(T))

static void SPCDECL element_destructor(void *pdata_v)
{
  struct element_data *pdata = (struct element_data*)pdata_v;
  FD_SETUP_SPENV(pdata->spenv)

  SP_free_globrefs(pdata->refbase,pdata->nrefs);
  SP_free(pdata);
}

/* Daemon for element/3: effectively disable Xi if i is not in the index domain */
static void SPCDECL 
element_daemon(Wam wam,
	       void *vdata,
	       SP_globref attr_ref,
	       TAGGED global)
{
  struct element_data *pdata = (struct element_data *)vdata;
  int eltno = (int)(((attr_ref - pdata->refbase)>>1)-1);
  
  dvar_init(DVAR(0), RefAttr(0), RefVar(0)); /* get Index */
  if (dvar_contains_value_l(DVAR(0),eltno))
    fd_enqueue_global(wam, global, 0x7/* [MC] 4.1: DOM, append*/);
}

/*
  '$fd_element'(+State0, +State, -Actions).
  State = state(Index,Value,Xs,NTargets,IsGround,Handle,Stamp)
  IsGround is 0 -> Xs is a list of Var-Mutable
  IsGround is 1 -> Xs is a list of integers
*/
void SPCDECL
prolog_fd_element(Wam wam,
			 SP_term_ref State0,
			 SP_term_ref State,
			 SP_term_ref Actions)
{
  int ent = -1;			/* initially disentailed */
  TAGGED handle, tvec, tisground;
  int i, ntargets, pivot = 0;
  SP_integer total_size;
  struct element_data *pdata;
  SP_BOOL committed;
  char *ptr;

  (void)State0;                 /* [PM] 3.9b5 avoid -Wunused */


/*    X(0) = RefTerm(State0); */
  dvar_export_start(wam);
  RefTerm(State) = fd_static_output_state(wam,&handle,&committed);
  DerefArg(tvec,X(0),4);	/* get NTargets */
  DerefArg(tisground,X(0),5);	/* get Isground */
  ntargets = GetSmall_int(tvec);
  if (ntargets==0) {
    goto ret;
  } else if (!IsVar(handle)) {		/* got [Flag | '$free'(Ptr)] */
    pdata = Pdata(struct element_data,handle);
  } else {			/* build persistent state */
    total_size = (ntargets+2)*sizeof(struct dvar);
    pdata = Palloc(struct element_data, total_size, handle);
    pdata->destructor = element_destructor;
    pdata->daemon = element_daemon;
    pdata->nrefs = tisground==TaggedZero ? (ntargets+2)<<1 : 4;
    FD_STORE_SPENV(pdata->spenv);
    pdata->refbase = SP_alloc_globrefs(pdata->nrefs);
    ptr = (char *)(pdata+1);
    pdata->dvar = (Dvar)ptr;
    ptr += (ntargets+2)*sizeof(struct dvar);
    SP_ASSERT(ptr == (char *)(pdata+1)+total_size);
    DerefArg(tvec,X(0),1);		/* get Index */
    fd_get_var_and_attr(tvec,RefAttr(0));
    DerefArg(tvec,X(0),2);		/* get Value */
    fd_get_var_and_attr(tvec,RefAttr(1));
    DerefArg(tvec,X(0),3);		/* get Xs */
    for (i=0; i<ntargets; i++) {
      TAGGED telt;
      DerefCar(telt,tvec);
      DerefCdr(tvec,tvec);
      if (tisground==TaggedZero) {
	fd_get_var_and_attr(telt,RefAttr(i+2));
	dvar_init(DVAR(i+2), RefAttr(i+2), RefVar(i+2));
      } else {
	DVAR(i+2)->min = DVAR(i+2)->max = telt;
	DVAR(i+2)->flags = DV_INTERVAL;
      }
    }
    if (tisground==TaggedZero)
      for (i=0; i<ntargets; i++)
	dvar_attach_daemon(wam, DVAR(i+2), pdata, X(1), fd.functor_dom); /* [MC] 4.1: wakeup on dom */
  }

  /* RESUME HERE */
  dvar_init(DVAR(0), RefAttr(0), RefVar(0));
  dvar_init(DVAR(1), RefAttr(1), RefVar(1));
  {
    TAGGED minofmin = Sup;
    TAGGED maxofmax = Inf;
    DVITER it;
    FDCONS cons;
    dviter_init(&it, DVAR(0));
    fdcons_init(&cons);
    while (!dviter_empty(&it)) {
      int ix = (int)dviter_next_value_l(&it)+1;
      Dvar dv = DVAR(ix);
      if (tisground==TaggedZero)
	dvar_init(dv, RefAttr(ix), RefVar(ix));    
      if (dvar_compare_set(dv,dvar_set(DVAR(1)))==FDI_DISJOINT) /* [MC] 4.1: no longer interval cmp */
	fdcons_add(wam, &cons,MakeSmall(ix-1));
      else {
	if (FDgt(minofmin,dvar_min_t(dv)))
	  minofmin = dvar_min_t(dv);
	if (FDlt(maxofmax,dvar_max_t(dv)))
	  maxofmax = dvar_max_t(dv);
      }
    }
    if (dvar_prune_set(DVAR(0), fdcons_set(&cons))<0)
      goto ret;
    if (dvar_fix_interval_t(DVAR(1), minofmin, maxofmax)<0)
      goto ret;
    if (dvar_is_integer(DVAR(0)))
      pivot = dvar_min_int(DVAR(0))+1;
    if (pivot>0 && tisground==TaggedZero) {
      if (dvar_fix_set(DVAR(1),dvar_set(DVAR(pivot)))<0 ||
	  dvar_fix_set(DVAR(pivot),dvar_set(DVAR(1)))<0)
	goto ret;
      dvar_pruning_done( DVAR(pivot));
    } else if (pivot>0) {
      if (dvar_fix_value_t(DVAR(1),dvar_min_t(DVAR(pivot)))<0)
	goto ret;
    }
    dvar_pruning_done( DVAR(0));
    dvar_pruning_done( DVAR(1));
    if (pivot>0 && tisground==TaggedZero)
      dvar_export( DVAR(pivot));
    dvar_export( DVAR(0));
    dvar_export( DVAR(1));
    if (minofmin==maxofmax) {
      ent = 1;
#if FD_EAGER_ALIAS
    } else if (pivot>0 && tisground==TaggedZero) {
      ent = 1;
    } else if (pivot>0) {
      ent = 1;
      dvar_export_equal(wam, DVAR(1), DVAR(pivot));
#endif
    } else {
      ent = 0;
    }
  }
 ret:
  if (ent==1)
    Pfree;
  dvar_export_done(wam,Actions, ent);
}

struct minmax_data {
  void (SPCDECL *destructor)(void *);
  void (SPCDECL *daemon)(Wam,void *,SP_globref,TAGGED); /* (wam,handle,attr_ref,global) */
  SPEnv *spenv;
  SP_globref refbase;
  int nrefs;
  int *target;
  Dvar dvar;
};

#define RefAttr(T) (pdata->refbase + 2*(T))
#define RefVar(T) (pdata->refbase + 2*(T) + 1)
#define TARGET(T) (pdata->target[T])
#define DVAR(T) (pdata->dvar+(T))

static void SPCDECL minmax_destructor(void *pdata_v)
{
  struct minmax_data *pdata = (struct minmax_data*)pdata_v;
  FD_SETUP_SPENV(pdata->spenv)

  SP_free_globrefs(pdata->refbase,pdata->nrefs);
  SP_free(pdata);
}

/* Daemon for minimum/2: effectively disable Xi that is for sure > Y */
/* Daemon for maximum/2: effectively disable Xi that is for sure < Y */
static void SPCDECL 
minmax_daemon(Wam wam,
	      void *vdata,
	      SP_globref attr_ref,
	      TAGGED global)
{
  struct minmax_data *pdata = (struct minmax_data *)vdata;
  TAGGED tstate;
  int varno, i, ntargets;

  varno = (int)((attr_ref - pdata->refbase)>>1);
  tstate = RefMutable(CTagToArg(global,1));
  DerefArg(tstate,tstate,3);	/* get NTargets */
  ntargets = GetSmall_int(tstate);
  for (i=0; i<ntargets; i++)
    if (TARGET(i)==varno)
      goto push;
  return;
 push:
  fd_enqueue_global(wam, global, 0x5/* MINMAX, append*/);
}

/*
  '$fd_minmax'(+State0, +State, -Actions).
  State = state(Y,Xs,NTargets,IsMax,Handle,Stamp)
  IsMax is 0 -> minimum/2
  IsMax is 1 -> maximum/2
*/
void SPCDECL
prolog_fd_minmax(Wam wam,
			       SP_term_ref State0,
			       SP_term_ref State,
			       SP_term_ref Actions)
{
  int ent = -1;			/* initially disentailed */
  TAGGED handle, tvec, tismax;
  TAGGED ymin, ymax;
  SP_integer state_stamp, total_size;
  int i, ntargets, count, pivot=0;
  struct minmax_data *pdata;
  SP_BOOL committed;
  char *ptr;

  (void)State0;                 /* [PM] 3.9b5 avoid -Wunused */


/*    X(0) = RefTerm(State0); */
  dvar_export_start(wam);
  RefTerm(State) = fd_unify_output_state(wam, &handle,&state_stamp,&committed);
  DerefArg(tvec,X(0),3);	/* get NTargets */
  DerefArg(tismax,X(0),4);	/* get IsMax */
  ntargets = GetSmall_int(tvec);
  if (ntargets==0) {
    goto ret;
  } else if (!IsVar(handle)) {		/* got [Flag | '$free'(Ptr)] */
    pdata = Pdata(struct minmax_data,handle);
  } else {			/* build persistent state */
    total_size = (ntargets+1)*(sizeof(int)+sizeof(struct dvar));
    pdata = Palloc(struct minmax_data, total_size, handle);
    pdata->destructor = minmax_destructor;
    pdata->daemon = minmax_daemon;
    pdata->nrefs = (ntargets+1)<<1;
    FD_STORE_SPENV(pdata->spenv);
    pdata->refbase = SP_alloc_globrefs((ntargets+1)<<1);
    ptr = (char *)(pdata+1);
    pdata->dvar = (Dvar)ptr;
    ptr += (ntargets+1)*sizeof(struct dvar);
    pdata->target = (int *)ptr;
    ptr += (ntargets+1)*sizeof(int);
    SP_ASSERT(ptr == (char *)(pdata+1)+total_size);
    DerefArg(tvec,X(0),1);		/* get Y */
    fd_get_var_and_attr(tvec,RefAttr(0));
    DerefArg(tvec,X(0),2);		/* get Xs */
    for (i=0; i<ntargets; i++) {
      TAGGED telt;
      DerefCar(telt,tvec);
      DerefCdr(tvec,tvec);
      TARGET(i) = i+1;
      fd_get_var_and_attr(telt,RefAttr(i+1));
    }
    for (i=0; i<ntargets; i++) {
      dvar_init(DVAR(i+1), RefAttr(i+1), RefVar(i+1));
      dvar_attach_daemon(wam, DVAR(i+1), pdata, X(1), fd.functor_minmax); /* [MC] 4.2.3: can GC */
    }
    CTagToArg(X(0),2) = atom_nil; /* [MC] 3.12: free for GC */
  }

  /* RESUME HERE */
  dvar_init(DVAR(0), RefAttr(0), RefVar(0));
  for (i=0; i<ntargets; i++) {
    int elt = TARGET(i);
    dvar_init(DVAR(elt), RefAttr(elt), RefVar(elt));
  }
 restart:
  count = 0;
  ymin = dvar_min_t(DVAR(0));
  ymax = dvar_max_t(DVAR(0));
  if (tismax==TaggedZero) {
    TAGGED minofmax = Sup;
    TAGGED minofmin = Sup;
    int rc;
    for (i=0; i<ntargets; i++) {
      int elt = TARGET(i);
      Dvar dv = DVAR(elt);
      if (dvar_fix_min_t(dv, ymin)<0) {
	goto ret;
      } else if (FDle(dvar_min_t(dv),ymax)) {
	count++;
	pivot = i;
	if (FDgt(minofmax,dvar_max_t(dv)))
	  minofmax = dvar_max_t(dv);
	if (FDgt(minofmin,dvar_min_t(dv)))
	  minofmin = dvar_min_t(dv);
      }
    }
    if (count==0)
      goto ret;
    rc = dvar_fix_interval_t(DVAR(0), minofmin, minofmax);
    if (rc<0) {
      goto ret;
    } else if (rc & DV_PRUNED_MAX) {
      goto restart;
    } else {
      ent = (minofmin==minofmax);
    }
  } else {
    TAGGED maxofmax = Inf;
    TAGGED maxofmin = Inf;
    int rc;
    for (i=0; i<ntargets; i++) {
      int elt = TARGET(i);
      Dvar dv = DVAR(elt);
      if (dvar_fix_max_t(dv, ymax)<0) {
	goto ret;
      } else if (FDle(ymin,dvar_max_t(dv))) {
	count++;
	pivot = i;
	if (FDlt(maxofmax,dvar_max_t(dv)))
	  maxofmax = dvar_max_t(dv);
	if (FDlt(maxofmin,dvar_min_t(dv)))
	  maxofmin = dvar_min_t(dv);
      }
    }
    if (count==0)
      goto ret;
    rc = dvar_fix_interval_t(DVAR(0), maxofmin, maxofmax);
    if (rc<0) {
      goto ret;
    } else if (rc & DV_PRUNED_MIN) {
      goto restart;
    } else {
      ent = (maxofmin==maxofmax);
    }
  }
  if (!ent && count==1) {
    Dvar dv = DVAR(TARGET(pivot));
    if (dvar_fix_set(DVAR(0),dvar_set(dv))<0 ||
	dvar_fix_set(dv,dvar_set(DVAR(0)))<0)
      goto ret;
  }
  dvar_pruning_done( DVAR(0));
  for (i=0; i<ntargets; i++) {
    int elt = TARGET(i);
    dvar_pruning_done( DVAR(elt));
  }
  dvar_export( DVAR(0));
  for (i=0; i<ntargets; i++) {
    int elt = TARGET(i);
    dvar_export( DVAR(elt));
  }
  if (ent==1) {
    Pfree;
  } else {
    int inf = 0;
    int sup = ntargets-1;
    int held = TARGET(sup);		/* sup is the hole */
    int current = TARGET(inf);
    
    while (inf<=sup) {
      if (tismax==TaggedZero ? FDge(ymax,dvar_min_t(DVAR(current)))
	                     : FDle(ymin,dvar_max_t(DVAR(current)))) {
	TARGET(inf) = current;
	inf++;
	current = (inf>=sup ? held : TARGET(inf));
      } else {
	TARGET(sup) = current;
	sup--;
	current = (inf>=sup ? held : TARGET(sup));
      }
    }
    CTagToArg(X(0),3) = MakeSmall(inf);
  }
 ret:
  dvar_export_done(wam,Actions, ent);
}

struct bool_channel_data {
  void (SPCDECL *destructor)(void *);
  void (SPCDECL *daemon)(Wam,void *,SP_globref,TAGGED); /* (wam,handle,attr_ref,global) */
  SPEnv *spenv;
  SP_globref refbase;
  int ntargets;
  int nrefs;
  SP_integer stamp;
  int top;
  int offset;
  int code;
  Dvar dvar;
  int *stack;
  char *sense;
};

static void SPCDECL bool_channel_destructor(void *pdata_v)
{
  struct bool_channel_data *pdata = (struct bool_channel_data*)pdata_v;
  FD_SETUP_SPENV(pdata->spenv)

  SP_free_globrefs(pdata->refbase,pdata->nrefs);
  SP_free(pdata);
}

static void SPCDECL 
bool_channel_daemon(Wam wam,
		    void *vdata,
		    SP_globref attr_ref,
		    TAGGED global)
{
  struct bool_channel_data *pdata = (struct bool_channel_data *)vdata;
  int ar, varno, state_stamp;
  TAGGED tstate;

  if (pdata->code & 2) {	/* #=, #\= */
    varno = (int)((attr_ref - pdata->refbase)>>1);
    tstate = RefMutable(CTagToArg(global,1));
    ar = Arity(TagToHeadfunctor(tstate));
    state_stamp = GetSmall_int(CTagToArg(tstate,ar));
    if (pdata->stamp!=state_stamp) { /* non-incremental */
      pdata->top = 0;
    }
    if (pdata->top==0) {
      SP_BOOL buried;
      (void)fd_daemon_copy_state(wam, &global,&buried);
      pdata->stamp = state_stamp+1;
    }
    SP_ASSERT(pdata->top < pdata->ntargets);
    if (varno>0)
      pdata->stack[pdata->top++] = varno;
  }
  fd_enqueue_global(wam, global, 0x5/* MINMAX, append*/);
}


static int bool_channel_eq(Wam wam, struct bool_channel_data *pdata,int sense)
{
  int pivot = 0, j, ent = -1;
  TAGGED tvec, tmin, tmax, curdom;
  FDITER it;
  
  dvar_init(DVAR(0), RefAttr(0), RefVar(0));
  for (j=0; j<pdata->top; j++) {
    int varno = pdata->stack[j];
    REF_GET_BOUNDS(RefAttr(varno), tmin, tmax);
    if (tmin==tmax) { /* can be false when posting */
      if (Tgtz(tmin)^pdata->sense[varno]^sense) {
	if (dvar_fix_value_l(DVAR(0),varno+pdata->offset-1)<0)
	  goto ret;
      } else {
	if (dvar_prune_value_l(DVAR(0),varno+pdata->offset-1)<0)
	  goto ret;
      }
    }
  }
  if (dvar_is_integer(DVAR(0))) {
    pivot = dvar_min_int(DVAR(0))-pdata->offset+1;
    if (pivot<1 || pivot>=pdata->ntargets)
      pivot = 0;
  }
  curdom = fd_localize(wam,dvar_set(DVAR(0)));
  tvec = fd_subtract(wam, CTagToArg(X(0),6),curdom); /* prev domain \ cur domain */
  tvec = fd_localize(wam,tvec);				       /* protect from GC */
  dvar_pruning_done( DVAR(0));
  dvar_export( DVAR(0));
  fditer_init(&it, tvec);
  while (!fditer_empty(&it)) {
    int varno = GetSmall_int(fditer_next(&it))-pdata->offset+1;
    if (!bool_export_value(wam, RefAttr(varno), RefVar(varno), pdata->sense[varno]^sense))
      goto ret;
  }  
  if (pivot) {
    if (!bool_export_value(wam, RefAttr(pivot), RefVar(pivot), pdata->sense[pivot]^sense^1))
      goto ret;
  }
  ent = !!dvar_is_integer(DVAR(0));
  if (!ent) {			/* update "prev domain" - slight overkill */
    TAGGED newdom = fd_intersection_interval(wam, curdom,
					     MakeSmall(pdata->offset),
					     MakeSmall(pdata->offset+pdata->ntargets-2));
    newdom = fd_globalize(wam,fd_localize(wam,newdom),0,3); /* beware of GC */
    CTagToArg(X(0),6) = newdom;
  }
 ret:
  pdata->top = 0;
  return ent;
}

/* sense=0 for #=<, 1 for #>= */
static int bool_channel_le(Wam wam,
			   struct bool_channel_data *pdata,
			   int sense, int yoff) 
{
  int i, ent = -1;
  int start01, start1, new01, new1; /* N.B. 1-based */
  SP_integer yminl, ymaxl;
  TAGGED ymint, ymaxt, tmin, tmax;

  dvar_init(DVAR(0), RefAttr(0), RefVar(0));
  new01 = start01 = GetSmall_int(CTagToArg(X(0),6));
  new1 = start1 = GetSmall_int(CTagToArg(X(0),7));

  /* prune from Xs to Y */
  for (i=start01; i<start1; i++) {
    REF_GET_BOUNDS(RefAttr(i), tmin, tmax);
    if (tmin==tmax && Tgtz(tmin)==(pdata->sense[i]^sense))
      new01 = i+1;
  }
  for (i=start1-1; i>=start01; i--) {
    REF_GET_BOUNDS(RefAttr(i), tmin, tmax);
    if (tmin==tmax && Tgtz(tmin)!=(pdata->sense[i]^sense))
      new1 = i;
  }
  if (start01<new01 && start1>new1) { /* found '0' and '1' */
    if (dvar_fix_interval_l(DVAR(0),
			    new01+pdata->offset-yoff-1,
			    new1+pdata->offset-yoff-1)<0)
      goto ret;
  } else if (start01<new01) { /* found '0' */
    if (dvar_fix_min_l(DVAR(0), new01+pdata->offset-yoff-1)<0)
      goto ret;
  } else if (start1>new1) { /* found '1' */
    if (dvar_fix_max_l(DVAR(0), new1+pdata->offset-yoff-1)<0)
      goto ret;
  }
  dvar_pruning_done( DVAR(0));
  dvar_export( DVAR(0));
  /* prune from Y to Xs */
  ymint = dvar_min_t(DVAR(0));
  ymaxt = dvar_max_t(DVAR(0));
  yminl = dvar_min_l(DVAR(0));
  ymaxl = dvar_max_l(DVAR(0));
  if (AreSmall(ymint,ymaxt) &&
      yminl >= pdata->offset-yoff &&
      ymaxl <= pdata->offset-yoff+pdata->ntargets-2) {
    new01 = (int)yminl-pdata->offset+yoff+1;
    new1 = (int)ymaxl-pdata->offset+yoff+1;
    for (i=start01; i<new01; i++)
      if (!bool_export_value(wam, RefAttr(i), RefVar(i), pdata->sense[i]^sense))
	goto ret;
    for (i=new1; i<start1; i++)
      if (!bool_export_value(wam, RefAttr(i), RefVar(i), pdata->sense[i]^sense^1))
	goto ret;
  } else if (IsSmall(ymint) && yminl >= pdata->offset-yoff) {
    new01 = new1 < yminl-pdata->offset+yoff+1 ? new1 : (int)yminl-pdata->offset+yoff+1;
    for (i=start01; i<new01; i++)
      if (!bool_export_value(wam, RefAttr(i), RefVar(i), pdata->sense[i]^sense))
	goto ret;
  } else if (IsSmall(ymaxt) && ymaxl <= pdata->offset-yoff+pdata->ntargets-2) {
    new1 = new01 > ymaxl-pdata->offset+yoff+1 ? new01 : (int)ymaxl-pdata->offset+yoff+1;
    for (i=new1; i<start1; i++)
      if (!bool_export_value(wam, RefAttr(i), RefVar(i), pdata->sense[i]^sense^1))
	goto ret;
  }
  CTagToArg(X(0),6) = MakeSmall(new01);
  CTagToArg(X(0),7) = MakeSmall(new1);
  ent = (new01==new1);
 ret:
  return ent;
}


/*
  FlatZinc accelerator:
  '$fd_bool_channel'(+State0, +State, -Actions).
  State = state(XAs,XSs,Y-YA,Offet,YSet,Handle,Stamp)
*/
void SPCDECL
prolog_fd_bool_channel(Wam wam,
		       SP_term_ref State0,
		       SP_term_ref State,
		       SP_term_ref Actions)
{
  int ent = -1;			/* initially disentailed */
  TAGGED handle, tvec, svec, susp;
  SP_integer state_stamp, total_size;
  int i, j, ntargets;
  struct bool_channel_data *pdata;
  SP_BOOL committed;
  char *ptr;

  (void)State0;                 /* [PM] 3.9b5 avoid -Wunused */


  /*    X(0) = RefTerm(State0); */
  dvar_export_start(wam);
  RefTerm(State) = fd_unify_output_state(wam,&handle,&state_stamp,&committed);
  if (!IsVar(handle)) {		/* got [Flag | '$free'(Ptr)] */
    pdata = Pdata(struct bool_channel_data,handle);
    ntargets = pdata->ntargets;
  } else {			/* build persistent state */
    DerefArg(tvec,X(0),1);	/* get Xs */
    ntargets = fd_list_length(tvec)+1;
    total_size = ntargets*(sizeof(struct dvar)+sizeof(int)+1);
    pdata = Palloc(struct bool_channel_data, total_size, handle);
    pdata->ntargets = ntargets;
    pdata->destructor = bool_channel_destructor;
    pdata->daemon = bool_channel_daemon;
    pdata->nrefs = ntargets<<1;
    FD_STORE_SPENV(pdata->spenv);
    pdata->refbase = SP_alloc_globrefs(ntargets<<1);
    ptr = (char *)(pdata+1);
    pdata->dvar = (Dvar)ptr;
    ptr += ntargets*sizeof(struct dvar);
    pdata->stack = (int *)ptr;
    ptr += ntargets*sizeof(int);
    pdata->sense = ptr;
    ptr += ntargets;
    SP_ASSERT(ptr == (char *)(pdata+1)+total_size);
    pdata->stamp = 0;
    DerefArg(tvec,X(0),1);		/* get Xs */
    DerefArg(svec,X(0),2);		/* get Ss */
    for (i=1; i<ntargets; i++) {
      TAGGED telt;
      DerefCar(telt,tvec);
      DerefCdr(tvec,tvec);
      fd_get_var_and_attr(telt,RefAttr(i));
      DerefCar(telt,svec);
      DerefCdr(svec,svec);
      pdata->sense[i] = (char)GetSmall(telt);
    }
    DerefArg(tvec,X(0),3);		/* get Y */
    fd_get_var_and_attr(tvec,RefAttr(0));
    DerefArg(tvec,X(0),4);		/* get Code */
    pdata->code = GetSmall_int(tvec);
    DerefArg(tvec,X(0),5);		/* get Offset */
    pdata->offset = GetSmall_int(tvec);
    susp = pdata->code & 2 ? fd.functor_dom : fd.functor_minmax;
    for (i=0, j=0; i<ntargets; i++) {
      dvar_init(DVAR(i), RefAttr(i), RefVar(i));
      dvar_attach_daemon(wam, DVAR(i), pdata, X(1), susp); /* [MC] 4.2.3: can GC */
      if (i>0 && pdata->code & 2)
	pdata->stack[j++] = i;
    }
    pdata->top = j;
    CTagToArg(X(0),1) = atom_nil; /* [MC] 3.12: free for GC */
    CTagToArg(X(0),2) = atom_nil; /* [MC] 3.12: free for GC */
  }

  /* RESUME HERE */
  pdata->stamp = state_stamp+1;
  switch (pdata->code) {
  case 0:
    ent = bool_channel_le(wam, pdata,0,0); /* #=< */
    break;
  case 1:
    ent = bool_channel_le(wam, pdata,1,1); /* #>= */
    break;
  case 2:
    ent = bool_channel_eq(wam, pdata,0); /* #= */
    break;
  case 3:
    ent = bool_channel_eq(wam, pdata,1); /* #\= */
    break;
  case 4:
    ent = bool_channel_le(wam, pdata,0,1); /* #< */
    break;
  case 5:
    ent = bool_channel_le(wam, pdata,1,0); /* #> */
    break;
  }
  if (ent==1) {
    Pfree;
  }
  dvar_export_done(wam, Actions, ent);
}

struct bool_data {
  void (SPCDECL *destructor)(void *);
  void (SPCDECL *daemon)(Wam,void *,SP_globref,TAGGED); /* (wam,handle,attr_ref,global) */
  SPEnv *spenv;
  SP_globref refbase;
  int ntargets;
  int nonground;
  int ac;
  int xone;
  int yzero;
  int nrefs;
  Dvar dvar;
  int *target;
  int *tloc;
  char *sense;
};

static void SPCDECL bool_destructor(void *pdata_v)
{
  struct bool_data *pdata = (struct bool_data*)pdata_v;
  FD_SETUP_SPENV(pdata->spenv)

  SP_free_globrefs(pdata->refbase,pdata->nrefs);
  SP_free(pdata);
}

static void SPCDECL 
bool_or_daemon(Wam wam,
	       void *vdata,
	       SP_globref attr_ref,
	       TAGGED global)
{
  struct bool_data *pdata = (struct bool_data *)vdata;
  int varno = (int)((attr_ref - pdata->refbase)>>1);
  int loc, swap;
  TAGGED tmin, tmax;
  SP_BOOL buried;
  TAGGED tstate = fd_daemon_copy_state(wam, &global,&buried);
  int nonground = pdata->ntargets - GetSmall_int(CTagToArg(tstate,3));
    
  if (pdata->nonground < nonground) { /* we have backtracked */
    pdata->xone = pdata->yzero = FALSE;
  }
  pdata->nonground = nonground;
  loc = pdata->tloc[varno];
  swap = pdata->target[--pdata->nonground];
  pdata->target[loc] = swap;
  pdata->tloc[swap] = loc;
  pdata->target[pdata->nonground] = varno;
  pdata->tloc[varno] = pdata->nonground;

  REF_GET_BOUNDS(attr_ref, tmin, tmax);
  (void)tmax;
  if (varno==0 && (Teqz(tmin) ^ pdata->sense[varno])) {
    pdata->yzero = TRUE;
  } else if (varno>0 && (Tgtz(tmin) ^ pdata->sense[varno])) {
    pdata->xone = TRUE;
  }
  CTagToArg(tstate,3) = MakeSmall(pdata->ntargets-pdata->nonground); /* update NGround */
  if (pdata->nonground<=1 || pdata->yzero || pdata->xone)
    fd_enqueue_global(wam, global, 0x5/* MINMAX, append*/);
}


/*
  FlatZinc accelerator:
  '$fd_bool_or'(+State0, +State, -Actions).
  State = state(Xs,Ss,NGround,Handle,Stamp)
*/
void SPCDECL
prolog_fd_bool_or(Wam wam,
		  SP_term_ref State0,
		  SP_term_ref State,
		  SP_term_ref Actions)
{
  int ent = -1;			/* initially disentailed */
  TAGGED handle, tvec, svec;
  SP_integer total_size, state_stamp;
  int i, j, k, ntargets;
  struct bool_data *pdata;
  SP_BOOL committed;
  char *ptr;

  (void)State0;                 /* [PM] 3.9b5 avoid -Wunused */


  /*    X(0) = RefTerm(State0); */
  dvar_export_start(wam);
  RefTerm(State) = fd_unify_output_state(wam, &handle,&state_stamp,&committed);
  if (!IsVar(handle)) {		/* got [Flag | '$free'(Ptr)] */
    pdata = Pdata(struct bool_data,handle);
    ntargets = pdata->ntargets;
  } else {			/* build persistent state */
    DerefArg(tvec,X(0),1);	/* get Xs */
    ntargets = fd_list_length(tvec);
    total_size = ntargets*(sizeof(struct dvar)+1) + 2*ntargets*sizeof(int);
    pdata = Palloc(struct bool_data, total_size, handle);
    pdata->ntargets = ntargets;
    pdata->destructor = bool_destructor;
    pdata->daemon = bool_or_daemon;
    pdata->nrefs = ntargets<<1;
    FD_STORE_SPENV(pdata->spenv);
    pdata->refbase = SP_alloc_globrefs(ntargets<<1);
    ptr = (char *)(pdata+1);
    pdata->target = (int *)ptr;
    ptr += ntargets*sizeof(int);
    pdata->tloc = (int *)ptr;
    ptr += ntargets*sizeof(int);
    pdata->dvar = (Dvar)ptr;
    ptr += ntargets*sizeof(struct dvar);
    pdata->sense = ptr;
    ptr += ntargets;
    SP_ASSERT(ptr == (char *)(pdata+1)+total_size);
    DerefArg(tvec,X(0),1);		/* get Xs */
    DerefArg(svec,X(0),2);		/* get Ss */
    for (i=0; i<ntargets; i++) {
      TAGGED telt;
      DerefCar(telt,tvec);
      DerefCdr(tvec,tvec);
      fd_get_var_and_attr(telt,RefAttr(i));
      DerefCar(telt,svec);
      DerefCdr(svec,svec);
      pdata->sense[i] = (char)GetSmall(telt);
    }
    pdata->yzero = pdata->xone = FALSE;
    for (i=0, j=0, k=ntargets; i<ntargets; i++) {
      dvar_init(DVAR(i), RefAttr(i), RefVar(i));
      dvar_attach_daemon(wam, DVAR(i), pdata, X(1), fd.functor_minmax); /* [MC] 4.2.3: can GC */
      if (dvar_is_integer(DVAR(i))) {
	pdata->tloc[i] = --k;
	pdata->target[k] = i;
	if (i==0 && ((dvar_min_l(DVAR(i))==0) ^ pdata->sense[i])) {
	  pdata->yzero = TRUE;
	} else if (i>0 && ((dvar_min_l(DVAR(i))>0) ^ pdata->sense[i])) {
	  pdata->xone = TRUE;
	}
      } else {
	pdata->tloc[i] = j;
	pdata->target[j++] = i;
      }
    }
    pdata->nonground = j;
    CTagToArg(X(0),1) = atom_nil; /* [MC] 3.12: free for GC */
    CTagToArg(X(0),2) = atom_nil; /* [MC] 3.12: free for GC */
  }

  /* RESUME HERE */
  if (pdata->xone) {
    if (pdata->yzero) {
      goto ret;
    } else {
      if (!bool_export_value(wam, RefAttr(0), RefVar(0), pdata->sense[0]^1)) /* may be 1 already */
	goto ret;
      ent = 1;
    }
  } else if (pdata->yzero) {
    for (i=0; i<pdata->nonground; i++) {
      int elt = pdata->target[i];
      if (!bool_export_value(wam, RefAttr(elt), RefVar(elt), pdata->sense[elt]))
	goto ret;
    }
    ent = 1;
  } else if (pdata->nonground==0) {
    TAGGED tmin, tmax;
    REF_GET_BOUNDS(RefAttr(0), tmin, tmax);
    (void)tmax;
    if (Tgtz(tmin) ^ pdata->sense[0])
      goto ret;
    ent = 1;
  } else if (pdata->nonground==1) {
    int elt = pdata->target[0];
    if (!bool_export_value(wam, RefAttr(elt), RefVar(elt), (elt>0)^pdata->sense[elt]))
      goto ret;
    ent = 1;
  } else {
    ent = 0;
  }
 ret:
  pdata->xone = pdata->yzero = FALSE;
  CTagToArg(X(0),3) = MakeSmall(pdata->ntargets-pdata->nonground); /* update NGround */
  if (ent==1) {
    Pfree;
  }
  dvar_export_done(wam, Actions, ent);
}

static void SPCDECL 
bool_xor_daemon(Wam wam,
		void *vdata,
		SP_globref attr_ref,
		TAGGED global)
{
  struct bool_data *pdata = (struct bool_data *)vdata;
  int varno = (int)((attr_ref - pdata->refbase)>>1);
  int loc, swap;
  TAGGED tmin, tmax;
  SP_BOOL buried;
  TAGGED tstate = fd_daemon_copy_state(wam, &global,&buried);
  
  pdata->nonground = pdata->ntargets - GetSmall_int(CTagToArg(tstate,3));
  pdata->ac = GetSmall_int(CTagToArg(tstate,4));
  loc = pdata->tloc[varno];
  swap = pdata->target[--pdata->nonground];
  pdata->target[loc] = swap;
  pdata->tloc[swap] = loc;
  pdata->target[pdata->nonground] = varno;
  pdata->tloc[varno] = pdata->nonground;

  REF_GET_BOUNDS(attr_ref, tmin, tmax);
  (void)tmax;
  pdata->ac += (Tgtz(tmin) ^ pdata->sense[varno]);
  CTagToArg(tstate,3) = MakeSmall(pdata->ntargets-pdata->nonground); /* update NGround */
  CTagToArg(tstate,4) = MakeSmall(pdata->ac); /* update NGround */
  if (pdata->nonground<=1)
    fd_enqueue_global(wam, global, 0x5/* MINMAX, append*/);
}


/*
  FlatZinc accelerator:
  '$fd_bool_xor'(+State0, +State, -Actions).
  State = state(Xs,Ss,NGround,Ac,Handle,Stamp)
*/
void SPCDECL
prolog_fd_bool_xor(Wam wam,
		   SP_term_ref State0,
		   SP_term_ref State,
		   SP_term_ref Actions)
{
  int ent = -1;			/* initially disentailed */
  TAGGED handle, tvec, svec;
  SP_integer total_size, state_stamp;
  int i, j, k, ntargets;
  struct bool_data *pdata;
  SP_BOOL committed;
  char *ptr;

  (void)State0;                 /* [PM] 3.9b5 avoid -Wunused */


  /*    X(0) = RefTerm(State0); */
  dvar_export_start(wam);
  RefTerm(State) = fd_unify_output_state(wam, &handle,&state_stamp,&committed);
  if (!IsVar(handle)) {		/* got [Flag | '$free'(Ptr)] */
    pdata = Pdata(struct bool_data,handle);
    ntargets = pdata->ntargets;
  } else {			/* build persistent state */
    DerefArg(tvec,X(0),1);	/* get Xs */
    ntargets = fd_list_length(tvec);
    total_size = ntargets*(sizeof(struct dvar)+1) + 2*ntargets*sizeof(int);
    pdata = Palloc(struct bool_data, total_size, handle);
    pdata->ntargets = ntargets;
    pdata->destructor = bool_destructor;
    pdata->daemon = bool_xor_daemon;
    pdata->nrefs = ntargets<<1;
    FD_STORE_SPENV(pdata->spenv);
    pdata->refbase = SP_alloc_globrefs(ntargets<<1);
    ptr = (char *)(pdata+1);
    pdata->target = (int *)ptr;
    ptr += ntargets*sizeof(int);
    pdata->tloc = (int *)ptr;
    ptr += ntargets*sizeof(int);
    pdata->dvar = (Dvar)ptr;
    ptr += ntargets*sizeof(struct dvar);
    pdata->sense = ptr;
    ptr += ntargets;
    SP_ASSERT(ptr == (char *)(pdata+1)+total_size);
    DerefArg(tvec,X(0),1);		/* get Xs */
    DerefArg(svec,X(0),2);		/* get Ss */
    for (i=0; i<ntargets; i++) {
      TAGGED telt;
      DerefCar(telt,tvec);
      DerefCdr(tvec,tvec);
      fd_get_var_and_attr(telt,RefAttr(i));
      DerefCar(telt,svec);
      DerefCdr(svec,svec);
      pdata->sense[i] = (char)GetSmall(telt);
    }
    pdata->ac = 0;
    for (i=0, j=0, k=ntargets; i<ntargets; i++) {
      dvar_init(DVAR(i), RefAttr(i), RefVar(i));
      dvar_attach_daemon(wam, DVAR(i), pdata, X(1), fd.functor_minmax); /* [MC] 4.2.3: can GC */
      if (dvar_is_integer(DVAR(i))) {
	pdata->tloc[i] = --k;
	pdata->target[k] = i;
	pdata->ac += (dvar_min_int(DVAR(i)) ^ pdata->sense[i]);
      } else {
	pdata->tloc[i] = j;
	pdata->target[j++] = i;
      }
    }
    pdata->nonground = j;
    CTagToArg(X(0),1) = atom_nil; /* [MC] 3.12: free for GC */
    CTagToArg(X(0),2) = atom_nil; /* [MC] 3.12: free for GC */
  }

  /* RESUME HERE */
  if (pdata->nonground==0) {
    if (pdata->ac & 1)
      goto ret;
    ent = 1;
  } else if (pdata->nonground==1) {
    int elt = pdata->target[0];
    if (!bool_export_value(wam, RefAttr(elt), RefVar(elt), (pdata->ac&1)^pdata->sense[elt]))
      goto ret;
    ent = 1;
  } else {
    ent = 0;
  }
  CTagToArg(X(0),3) = MakeSmall(pdata->ntargets-pdata->nonground); /* update NGround */
  CTagToArg(X(0),4) = MakeSmall(pdata->ac); /* update Ac */
  if (ent==1) {
    Pfree;
  }
 ret:
  dvar_export_done(wam, Actions, ent);
}

