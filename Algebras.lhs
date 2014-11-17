          ********************************************
          *         Evaluation Algebras              *
          *                                          *
          *       Algebra type, enumeration,         *
          *   cross product, counting, energy,       *
          *       base pair maximization             *
          ********************************************

1. Algebra type
2. Counting  (*)
3. Enumeration
 a) with indices
 b) with nucleotides (*)
4. Energy maximization
5. base pair maximization
6. prettyprint (dot-bracket)
7. connect format
8. ***-operator

(*) moved to Algebras2.lhs
 
> module Algebras where

> import Array
> import List
> import RNACombinators
> import Foldingspace
> import Energy
> import Intloop
> import Intloop21
> import Intloop22

1. Algebra type

> type FS_Algebra base  comp cmpl = (   
>            base -> cmpl -> cmpl ,  -- sadd
>	     comp -> cmpl -> cmpl ,  -- cadd

>	     base -> comp -> base -> comp, --is
>	     base -> comp -> base -> comp, --sr
>	     base -> base -> Region -> base -> base         -> comp,   --hl
>	     base -> base -> Region -> comp -> base -> base -> comp,   --bl
>	     base -> base -> comp -> Region -> base -> base -> comp,   --br
>	     base -> base -> Region -> comp -> Region -> base -> base -> comp, --il

>	     base-> base->        (cmpl,cmpl)       -> base-> base -> comp,--ml
>	     base-> base-> base ->(cmpl,cmpl)	    -> base-> base -> comp,--mldl
>	     base-> base->        (cmpl,cmpl)-> base-> base-> base -> comp,--mldr
>	     base-> base-> base ->(cmpl,cmpl)-> base-> base-> base -> comp,--mldlr

>	     base -> comp -> base -> comp, --dl
>	     base -> comp -> base -> comp, --dr
>	     base -> comp -> base -> comp, --dlr
>	     base -> comp -> base -> comp, --edl
>	     base -> comp -> base -> comp, --edr
>	     base -> comp -> base -> comp, --edlr
>	     comp -> comp,		   -- drem
>	     cmpl -> cmpl -> cmpl,     -- cons (in fact it is append)
>	     comp ->  cmpl,	       -- ul
>	     comp ->  cmpl,	       -- pul
>	     cmpl -> Region -> cmpl,   -- addss
>	     Region -> comp -> cmpl,   -- ssadd

>	     cmpl,  --nil
>	     [comp] -> [comp],  --h
>	     [cmpl] -> [cmpl],  --h_l
>	     [cmpl] -> [cmpl],  --h_s
>	     [(comp, Int,Int)] -> [(comp, Int,Int)],  --h_i
>	     [(comp, Int, Int)]-> [(comp, Int, Int)] -- h_p
>	   )                              -- ghc handles only up to 34-tuples, so we split the 
>					  -- algebra into two parts
> type FS_AlgebraExt base  comp cmpl = (    			    
>	             (comp, Int, Int)		  -> comp, -- pk
>	     base -> (comp, Int, Int)		  -> cmpl, -- pkmldl
>	             (comp, Int, Int) -> base	  -> cmpl, -- pkmldr
>	     base -> (comp, Int, Int) -> base	  -> cmpl, -- pkmldlr
>                    (comp, Int, Int)		  -> cmpl, -- pkml
>
>	     Int -> Region -> cmpl -> Region -> cmpl -> 
>		      Region -> cmpl -> Region  -> (Int,Int) -> (comp, Int, Int), -- pk'
>	     
>	     base -> (comp, Int, Int)         -> comp, -- kndl
>	             (comp, Int, Int) -> base -> comp, -- kndr 
>	     base -> (comp, Int, Int) -> base -> comp, -- kndlr

>	     Int ->  cmpl -> base -> cmpl, -- frd
>	     Int ->  base -> cmpl -> cmpl, -- bkd
>	     base -> (comp, Int, Int) -> base	 -> (comp,Int), -- scale
>	     (comp,Int) -> comp,		  --unscale

>	     Int -> Int -> Region		 -> [cmpl], --emptymid
>	     Int -> Int -> Region		 -> [cmpl], --midbase
>	     Int -> Int -> Region		 -> [cmpl], --middlro
>	     Int ->	    base -> cmpl	 -> cmpl,   --middl
>		    Int -> 	    cmpl -> base -> cmpl,   --middr
>	     Int -> Int ->  base -> cmpl -> base -> cmpl,   --middlr
>	     cmpl -> cmpl,     --midregion
>	     Region -> comp)   --pss	      
>	     
 

===================================
3.a Enum Algebra
===================================

> enum :: (RNAInput -> FS_Algebra    Int (Component Ibase) [(Component Ibase)],
>	   RNAInput -> FS_AlgebraExt Int (Component Ibase) [(Component Ibase)])

> enum  = (enumalg , enumalgext)

> enumalg :: RNAInput -> FS_Algebra Int (Component Ibase) [(Component Ibase)]
> enumalg inp =  (sadd,cadd,is,sr,hl,bl,br, il,
>	          ml, mldl, mldr, mldlr, dl, dr, dlr, edl, edr, edlr,
>		  drem, cons, ul, pul, addss, ssadd, nil, h, h_l, h_s, h_i, h_p)
>     where
>       sadd  lb ((SS (x,y)):xs) = SS (lb-1,y) :xs
>	sadd  lb e               = SS (lb-1,lb) : e
>	cadd  x  e               = x : e

>	is  lloc  e rloc	   =  e
>	sr   lb  e rb		   = (SR lb e rb)
>	hl  llb lb r rb rrb	   = (SR llb (HL lb r rb) rrb)
>	bl  llb bl x r br rrb	   = (SR llb (BL bl x r br) rrb)
>	br  llb bl r x br rrb	   = (SR llb (BR bl r x br) rrb)
>	il llb lb lr x rr rb rrb   = (SR llb (IL lb lr x rr rb) rrb)

>	ml    llb bl    (c1,c) br rrb    =(SR llb (ML   bl    (c1 ++ c)    br) rrb)
>	mldl  llb bl dl (c1,c) br rrb    =(SR llb (MLL  bl dl (c1 ++ c)    br) rrb)
>	mldr  llb bl (c1,c) dr br rrb    =(SR llb (MLR  bl    (c1 ++ c) dr br) rrb)
>	mldlr llb bl dl (c1,c) dr br rrb =(SR llb (MLLR bl dl (c1 ++ c) dr br) rrb)
>	dl   dl c _                = DL  dl c
>	dr   _  c dr		   = DR     c dr
>	dlr  dl c dr		   = DLR dl c dr
>	edl  dl c _		   = EDL dl c
>	edr  _  c dr		   = EDR    c dr
>	edlr  dl c dr		   = EDLR dl c dr
>	drem  c		   = c

>	cons  c1 c = c1 ++ c
>	ul  c1 = [c1]
>	pul  c1 = [c1]
>	addss  c1 r = c1 ++ [SS r]
>	ssadd  r x = [(SS r) , x]
>	nil = []
 
>	h es   = es
>	h_l es = es
>	h_s es = es
>	h_i es = es
>	h_p es = es

> enumalgext:: RNAInput ->FS_AlgebraExt Ibase (Component Ibase) [(Component Ibase)]

> enumalgext inp= (pk, pkmldl, pkmldr, pkmldlr, pkml, pk',
>		  kndl, kndr,  kndlr, frd, bkd, scale, unscale,
>		  emptymid, midbase, middlro, middl, middr, middlr, midregion, pss)
>		  where
>	pk          (c,_,_)	=	  c
>	pkmldl   lb (c,_,_)    = [DL  lb c]
>	pkmldr      (c,_,_) rb = [DR     c rb]
>	pkmldlr  lb (c,_,_) rb = [DLR lb c rb]
>	pkml	    (c,_,_)    =	 [c]

>	pk'  _ a@(i,j) u b v a' w b'@(k,l) _ = (PK a ((SS (j,j+1)):u) b (compact v) a' 
>						 (w ++[SS (k-2,k)]) b', 0, 0)

>	kndl    lb (c,_,_)    = DL lb c
>	kndr       (c,_,_) rb = DR    c rb
>	kndlr   lb (c,_,_) rb = DLR lb c rb

>	frd  _    (c:cs) rb = (DR c rb):cs
>	bkd  _ lb  (c:cs)   = (DL lb c):cs

>	scale   i (c,k,l) j =  (c,j-i)
>	unscale (c,l) = c

>	emptymid _ _ (i,j)	= [[]| i   ==j]
>	midbase  _ _ (i,j)	= [[SS (i,j)]| i+1 ==j]
>	middlro  _ _ (i,j)	= [[SS (i,j)]| i+2 ==j]
>	middl    _   lb  (c:cs)	= (DL lb c):cs
>	middr      _	 (c:cs) rb	= (DR c rb):cs
>	middlr   _ _ lb (c:cs) rb	= (DLR lb c rb):cs
>	midregion  c		= c
>	pss r		        = SS r


=============================
4. Energy Algebra
=============================

> energy :: (RNAInput -> FS_Algebra Int Int Int, RNAInput -> FS_AlgebraExt Int Int Int)
> energy  = (energyalg , energyalgext)

> energyalg :: RNAInput -> FS_Algebra Int Int Int
> energyalg inp =  (sadd,cadd,is,sr,hl,bl,br, il,
>	       ml, mldl, mldr, mldlr, dl, dr, dlr, edl, edr, edlr,
>	       drem, cons, ul, pul, addss, ssadd, nil, h, h_l, h_s, h_i,h_p)

>     where
>       sadd  lb e = e
>	cadd  e1 e = e1 + e

>	is  lloc     e rloc    = e  + termaupenalty (inp!(lloc+1)) (inp!(rloc))
>	sr  lb       e rb     = e + sr_energy inp (lb,rb)
>	hl  llb lb _   rb rrb =     hl_energy inp (lb,rb) + sr_energy inp (llb,rrb) 
>	bl  llb bl x e br rrb = e + bl_energy inp bl x br + sr_energy inp (llb,rrb)
>	br  llb bl e x br rrb = e + br_energy inp bl x br + sr_energy inp (llb,rrb)
>	il llb lb lr e rr rb rrb    = e + sr_energy inp (llb,rrb) + il_energy inp lr rr

>	ml    llb bl    (e1,e)    br rrb = 380 + e1 + e + sr_energy inp (llb,rrb) + termaupenalty (inp!bl) (inp!br)
>	mldl  llb bl dl (e1,e)    br rrb = 380 + e1 + e + dli_energy inp (bl,br) + sr_energy inp (llb,rrb)
>					       + termaupenalty (inp!bl) (inp!br)
>	mldr  llb bl    (e1,e) dr br rrb = 380 + e1 + e + dri_energy inp (bl,br) + sr_energy inp (llb,rrb)
>					       + termaupenalty (inp!bl) (inp!br)
>	mldlr llb bl dl (e1,e) dr br rrb = 380 + e1 + e + dli_energy inp (bl,br)
>			       			        + dri_energy inp (bl,br) + sr_energy inp (llb,rrb) 
>							+ termaupenalty (inp!bl) (inp!br)
> 
>	dl    dl e rloc = e + dl_energy inp (dl+1,rloc)
>	dr  lloc e dr   = e + dr_energy inp (lloc+1,dr-1)
>	dlr   dl e dr   = e + dl_energy inp (dl+1,dr-1) + dr_energy inp (dl+1,dr-1)
>	edl   dl e rloc = e + dl_energy inp (dl+1,rloc) + termaupenalty (inp!(dl+1)) (inp!rloc)
>	edr lloc e dr   = e + dr_energy inp (lloc+1,dr-1) + termaupenalty (inp!(lloc+1)) (inp!(dr-1))
>	edlr  dl e dr   = e + dl_energy inp (dl+1,dr-1) + dr_energy inp (dl+1,dr-1) + termaupenalty (inp!(dl+1)) (inp!(dr-1))
>	drem     e      = e 

>	cons  e1 e   = e1 + e
>	addss    e r =      e + ss_energy r
>	ul       e   = 40 + e
>	pul      e   =      e
>	ssadd r  e   = 40 + e + ss_energy r
>	nil = 0
>
>	h   [] = []
>	h   es = [minimum es]
>	h_l [] = []
>	h_l es = [minimum es]
>	h_s [] = []
>	h_s es = [minimum es] 
>	h_i [] = []
>	h_i es = [minimum es] -- tuples are sorted by the first component, that is the energy
>	h_p [] = []
>       h_p es = [minimum es]

> energyalgext :: RNAInput -> FS_AlgebraExt Int Int Int
> energyalgext inp = (pk, pkmldl, pkmldr, pkmldlr, pkml, pk',
>	       kndl, kndr,  kndlr, frd, bkd, scale, unscale, emptymid,
>	       midbase, middlro, middl, middr, middlr, midregion, pss)
>	       where

>	pk         (e,k,l)     = e
>	pkmldl  lb (e,k,l)     = e + 600 + wkn *  dl_energy inp (lb+1,l)
>	pkmldr     (e,k,l) rb  = e + 600 + wkn *  dr_energy inp (k+1,rb-1) 
>	pkmldlr lb (e,k,l) rb  = e + 600 + wkn * (dl_energy inp (lb+1,l) + dr_energy inp (k+1,rb-1))
>	pkml       (e,k,l)     = e + 600
 
>	pk' e a fro b'@(i',_) mid a'@(k,l) bac b _ = 
>					   (pkinit + e + 3*npp +  fro +  mid +  bac 
>                                                  + dangles inp a b' a' b, i',l)
 								
>	kndr      (e,k,l) rb  = e +   npp + wkn * dr_energy inp (k+1,rb-1)
>	kndl   lb (e,k,l)     = e +   npp + wkn * dl_energy inp (lb+1,l)
>	kndlr  lb (e,k,l) rb  = e + 2*npp + wkn * (dl_energy inp (lb+1,l)+ dr_energy inp (k+1,rb-1))

>	frd j e base = e+ wkn * dl_energy inp (base+1,j) + npp     -- base dangling of pseudoknot stem
>	bkd i   base e = e+ wkn * dr_energy inp (i+1,base-1) + npp    -- base dangling of pseudoknot stem
>
>	scale    i (e,k,l) j =  ((1000 *e) `div` (j-i),(j-i))
>	unscale     (e,i)    = e*(fromIntegral i) `div` 1000

>	emptymid k l (i,j) = [ wkn * stack_dg (inp!l) (inp!(k+1)) (inp!i) (inp!(i+1))       |  i==j]
>	midbase  k l (i,j) = [ wkn * stack_dg (inp!l) (inp!(k+1)) (inp!i) (inp!(i+2)) + npp |i+1==j]
>	middlro  k l (i,j) = [ 2*npp + wkn *  (dri_energy inp (l,i+3)+ dli_energy inp (i,k+1)) | i+2==j]
 
>	middl  k   lb e    = e+ npp + wkn * dli_energy inp (lb-1,k+1) 
>	middr    l    e rb = e+ npp + wkn * dri_energy inp (l,rb+1)
>	middlr k l lb e rb = e+ 2*npp + wkn *  (dri_energy inp (l,rb+1)+ dli_energy inp (lb-1,k+1))

>	midregion e = e
>	pss  r	    = sspenalty (sizeof r)



======================================
5. Basepairmaximization
======================================

> bp :: (RNAInput -> FS_Algebra Int Int Int, RNAInput -> FS_AlgebraExt Int Int Int)
> bp = (basepairalg , basepairalgext)

> basepairalg :: RNAInput -> FS_Algebra Int Int Int
> basepairalg inp = (sadd,cadd,is,sr,hl,bl,br, il, ml, mldl, mldr, mldlr, dl, dr, dlr, edl, edr, edlr,
>	             drem, cons, ul, pul, addss, ssadd, nil, h, h_l, h_s, h_i,h_p)

>     where
>	sadd  lb e  = e		
>	cadd  x  e  = x + e

>	is  lb e rb = e	
>	sr  lb e rb = e + 1	
>	hl  llb lb r   rb rrb = 2	
>	bl  llb bl x e br rrb = 2 + e	
>	br  llb bl e x br rrb = 2 + e	
>	il _ _ _  x _ _ _      = x + 2 

>	ml    llb bl    (x1,x)    br rrb = x1 + x + 2 
>	mldl  llb bl dl (x1,x)    br rrb = x1 + x + 2
>	mldr  llb bl    (x1,x) dr br rrb = x1 + x + 2
>	mldlr llb bl dl (x1,x) dr br rrb = x1 + x + 2
>	dl    dl x _  = x	  
>	dr    _  x dr = x	  
>	dlr   dl x dr = x	  
>	edl   dl x _  = x	  
>	edr   _  x dr = x	  
>	edlr  dl x dr = x	  
>	drem     x    = x	  

>	cons  c1 c = c1 + c
>	ul  c1 = c1
>	pul  c1 = c1
>	addss  c1 r = c1	
>	ssadd  r x = x		
>	nil = 0
 
>	h [] = []
>	h es = [maximum es]
>       h_l [] = []
>	h_l es = [maximum es]
>	h_s [] = []
>	h_s es = [maximum es]
>	h_i [] = []
>	h_i es = [maximum es]
>	h_p [] = []
>	h_p es = [maximum es]

> basepairalgext :: RNAInput -> FS_AlgebraExt Int Int Int
> basepairalgext inp =(pk, pkmldl, pkmldr, pkmldlr, pkml, pk',
>		   kndl, kndr,  kndlr, frd, bkd, scale, unscale, emptymid, 
>		   midbase, middlro, middl, middr, middlr, midregion, pss)	
>		where

>	pk	   (c,_,_)   = c
>	pkmldl   _ (c,_,_)   = c
>	pkmldr     (c,_,_) _ = c
>	pkmldlr  _ (c,_,_) _ = c
>	pkml	   (c,_,_)   = c

>	pk'  _ a u b v a' w b' _ = (u+v+w+ (min (sizeof a) (sizeof a')) + (min (sizeof b) (sizeof b')) ,fst b, snd a')      
>	kndl    _ (c,_,_)   = c
>	kndr      (c,_,_) _ = c
>	kndlr   _ (c,_,_) _ = c

>	frd _     c _ = c
>	bkd _  _  c   = c

>	scale    i (c,k,l) j =  (c,(j-i))  
>	unscale (c,l) = c

>	emptymid _ _ (i,j)	= [0| i   ==j]
>	midbase  _ _ (i,j)	= [0| i+1 ==j]
>	middlro  _ _ (i,j)	= [0| i+2 ==j] 
>	middl    _    _  c	= c
>	middr    _   	 c _	= c
>	middlr   _ _  _  c _    = c
>	midregion  c		= c
>	pss  r			= 0


===================================
6 Prettyprint Algebra (dot bracket notation)
===================================

> pp :: ( RNAInput -> FS_Algebra Int [Char] [Char], RNAInput -> FS_AlgebraExt Int [Char] [Char])
> pp  = (prettyprintalg , prettyprintext )

> prettyprintalg :: RNAInput -> FS_Algebra Int [Char] [Char]
> prettyprintalg inp = (sadd,cadd,is,sr,hl,bl,br, il,ml, mldl, mldr, mldlr, dl, dr, dlr, edl, edr, edlr,
>		   drem, cons, ul, pul, addss, ssadd, nil, h, h_l, h_s, h_i, h_p)
 
>     where
>	sadd  lb e = "." ++ e		
>	cadd  x  e = x ++ e

>	is _ x _ = x
>	sr  lb e rb = "(" ++ e ++ ")"	
>	hl  llb lb r   rb rrb = "((" ++ dots r ++"))"	
>	bl  llb bl x e br rrb = "((" ++ dots x ++ e ++"))"
>	br  llb bl e x br rrb = "((" ++ e ++ dots x ++"))"
>	il  llb lb lr x rr rb rrb = "((" ++ dots lr  ++ x ++ dots rr ++ "))" 

>	ml    llb bl    (x1,x)    br rrb = "((" ++ x1 ++ x ++ "))" 
>	mldl  llb bl dl (x1,x)    br rrb = "((."++ x1 ++ x ++ "))"
>	mldr  llb bl    (x1,x) dr br rrb = "((" ++ x1 ++ x ++ ".))" 
>	mldlr llb bl dl (x1,x) dr br rrb = "((."++ x1 ++ x ++ ".))"
>	dl    dl x _  = "."++ x	  
>	dr    _  x dr =       x ++"."	  
>	dlr   dl x dr = "."++ x ++"."	  
>	edl   dl x _  = "."++ x	  
>	edr   _  x dr =       x ++"."	  
>	edlr  dl x dr = "."++ x ++"."	       
>	drem     x    = x	  

>	cons  c1 c = c1 ++ c
>	ul  c1 = c1
>	pul  c1 = c1
>	addss  c1 r = c1 ++ dots r
>	ssadd  r x = dots r ++ x		
>	nil = []
 
>	h [] = []
>	h es = es
>       h_l [] = []
>	h_l es = es
>	h_s [] = []
>	h_s es = es
>	h_i [] = []
>	h_i es = es
>	h_p [] = []
>	h_p es = es

> prettyprintext :: RNAInput -> FS_AlgebraExt Int [Char] [Char]
> prettyprintext inp =(pk, pkmldl, pkmldr, pkmldlr, pkml, pk',
>		   kndl, kndr,  kndlr, frd, bkd, scale, unscale, emptymid,
>		   midbase, middlro, middl, middr, middlr, midregion, pss)	
>		where

>	pk	   (c,_,_)   = c
>	pkmldl   _ (c,_,_)   = "." ++c
>	pkmldr     (c,_,_) _ = c ++ "."
>	pkmldlr  _ (c,_,_) _ = "." ++ c ++ "."
>	pkml	   (c,_,_)   = c

>	pk'  _ a u b v a' w b' (adangle,bdangle) = ((app ++ "." ++ u ++ bpp ++ v ++
>                                         app' ++ w ++ ".." ++ bpp' ),0,0)
>			  where (app, app')
>				      | adangle == 0    = (open1 a, close1 a')
>				      | isin a adangle  = (f a adangle '[', close1 a')
>				      | isin a' adangle = (open1 a, f a' adangle ']')
>			        (bpp, bpp') 
>				      | bdangle == 0    =  (open2 b, close2 b')
>				      | isin b bdangle  =  (f b bdangle '{', close2 b')
>				      | isin b' bdangle =  (open2 b,  f b' bdangle '}')

>			        isin (i,j) d | d>i && d<j = True
>					     | otherwise  = False 
>				f (i,j) dangle char = [ if (x==dangle) then '.' else char| x<-[i+1 .. j]]	
>

>	kndl    _ (c,_,_)   = "." ++ c
>	kndr      (c,_,_) _ = c ++ "."
>	kndlr   _ (c,_,_) _ = "." ++ c ++ "."

>	frd _     c _ = c ++"."
>	bkd _  _  c   = "." ++ c 

>       skipleft _ c    = c
>	skipright  c _  = c
>	scale    i (c,k,l) j =  (c,j-i)
>	unscale (c,l) = c

>	emptymid _ _ (i,j)	= [[]  | i   ==j]
>	midbase  _ _ (i,j)	= ["." | i+1 ==j]
>	middlro  _ _ (i,j)	= [".."| i+2 ==j] 
>	middl    _    _ c	= "."++ c
>	middr    _   	c _	=  c ++ "."
>	middlr   _ _  _ c _     = "." ++ c ++ "."
>	midregion  c		= c
>	pss  r			= dots r

=============================
8. ***-operator - combines two algebras
=============================

> infix ****, *****
> infixr ***

> (*****) :: (Eq comp, Eq cmpl, Ord comp2, Ord cmpl2, Ord comp, Ord cmpl)=> (RNAInput -> FS_Algebra Int comp cmpl) ->
>				 (RNAInput -> FS_Algebra Int comp2 cmpl2)
>			       -> RNAInput -> FS_Algebra Int (comp,comp2) (cmpl,cmpl2) 

> (alg1 ***** alg2) inp =  (sadd,cadd,is,sr,hl,bl,br, il,
>		       ml, mldl, mldr, mldlr, dl, dr, dlr, edl, edr, edlr,
>		       drem, cons, ul, pul, addss, ssadd, nil, h, h_l, h_s, h_i, h_p)
>     where
>       (sadd1,cadd1,is1,sr1,hl1,bl1,br1, il1,
>        ml1, mldl1, mldr1, mldlr1, dl1, dr1, dlr1, edl1, edr1, edlr1,
>	 drem1, cons1, ul1, pul1, addss1, ssadd1, nil1, h1, h_l1, h_s1, h_i1, h_p1) = alg1 inp
>       (sadd2,cadd2,is2,sr2,hl2,bl2,br2, il2,
>        ml2, mldl2, mldr2, mldlr2, dl2, dr2, dlr2, edl2, edr2, edlr2,
>	 drem2, cons2, ul2, pul2, addss2, ssadd2, nil2, h2, h_l2, h_s2, h_i2, h_p2) = alg2 inp
>
>	sadd  lb (c,d)            = (sadd1 lb c, sadd2 lb d)
>	cadd (c1,c2) (a1,a2) = (cadd1 c1 a1, cadd2 c2 a2)
>	is	   = com3 is1 is2
>	sr 	   = com3 sr1 sr2 
>	hl llb lb r rb rrb	     = (hl1 llb lb    r    rb rrb, hl2 llb lb r rb    rrb)
>	bl llb bl x (c,d) br rrb     = (bl1 llb bl  x c    br rrb, bl2 llb bl x  d br rrb)
>	br llb bl (c,d) x br rrb     = (br1 llb bl    c x  br rrb, br2 llb bl d  x br rrb)
>	il llb lb lr (c,d) rr rb rrb = (il1 llb lb lr c rr rb rrb, il2 llb lb lr d rr rb rrb)

>	ml  llb bl ((a,c1),(b,c)) br rrb          = (ml1    llb bl    (a,b) br rrb   , ml2    llb bl    (c1, c)    br rrb)
>	mldl  llb bl dl ((a,c1),(b,c)) br rrb     = (mldl1  llb bl dl (a,b) br rrb   , mldl2  llb bl dl (c1, c)    br rrb)
>	mldr  llb bl ((a,c1),(b,c)) dr br rrb     = (mldr1  llb bl    (a,b) dr br rrb, mldr2  llb bl    (c1, c) dr br rrb)
>	mldlr  llb bl dl ((a,c1),(b,c)) dr br rrb = (mldlr1 llb bl dl (a,b) dr br rrb, mldlr2 llb bl dl (c1, c) dr br rrb)
>	dl    l (c,d) r = (dl1    l c r, dl2   l d r)
>	dr    l (c,d) r = (dr1    l c r, dr2   l d r)  
>	dlr   l (c,d) r = (dlr1   l c r, dlr2  l d r)
>	edl   l (c,d) r = (edl1   l c r, edl2  l d r)
>	edr   l (c,d) r = (edr1   l c r, edr2  l d r)  
>	edlr  l (c,d) r = (edlr1  l c r, edlr2 l d r)
>	drem    (c,d)   = (drem1  c, drem2 d)

>	cons  (a,c1) (b,c) = (cons1   a b,cons2   c1 c)
>	ul   (a,c1)	   = (ul1     a  , ul2	  c1  )
>	pul  (a,c1)	   = (pul1    a  , pul2	  c1  )
>	addss  (a,c1) r	   = (addss1  a r, addss2 c1 r)
>	ssadd  r (c,d)	   = (ssadd1  r c, ssadd2 r d )
>	nil = (nil1,nil2)

       h xs = [(x1,x2)| x1 <- nub $ h1 [ y1 | (y1,y2) <- xs],
                     x2 <-       h2 [ y2 | (y1,y2) <- xs, y1 == x1]]

these are very special choice functions that might be too general in another context.
However for the case of energy minimization it is sufficient (and fast).

>	h xs   = take 1 [(a,b)| (a,b)<- xs, elem a (h1 (map fst xs))]

>	h_l xs = take 1 [(a,b)| (a,b)<- xs, elem a (h_l1 (map fst xs))]
>	h_s xs = take 1 [(a,b)| (a,b)<- xs, elem a (h_s1 (map fst xs))]
>	h_i xs = take 1 [((a,b),c,d)| ((a,b),c,d) <- xs, elem (a,c,d) (h_i1 x)]
>		    where x = [(x,k,asym) |((x,y),k,asym) <- xs]
>	h_p xs = take 1 [((a,b),c,d)| ((a,b),c,d) <- xs, elem a (h1 (map (fst.fst') xs))] 

> (****) ::  (Eq comp1, Eq cmpl1, Eq comp2, Eq cmpl2) => 
>			(RNAInput -> FS_AlgebraExt base comp1 cmpl1) ->
>		        (RNAInput -> FS_AlgebraExt base comp2 cmpl2) -> RNAInput
>				  -> FS_AlgebraExt base (comp1,comp2) (cmpl1,cmpl2) 
> (alg1ext **** alg2ext) inp =  
>	      (pk, pkmldl, pkmldr, pkmldlr, pkml, pk2,
>	       kndl, kndr,  kndlr, frd, bkd, scale, unscale,
>	       emptymid, midbase, middlro, middl, middr, middlr, midregion, pss)
>		  where
>	(pk', pkmldl', pkmldr', pkmldlr', pkml', pk2',
>	 kndl', kndr',  kndlr', frd', bkd',  scale', unscale',  
>	 emptymid', midbase', middlro', middl', middr', middlr', midregion', pss')
>			      = alg1ext inp
>	(pk'', pkmldl'', pkmldr'', pkmldlr'', pkml'', pk2'',
>	 kndl'', kndr'',  kndlr'', frd'', bkd'', scale'', unscale'',  
>	 emptymid'', midbase'', middlro'', middl'', middr'', middlr'', midregion'', pss'')
>			      = alg2ext inp

>	pk          ((c,d),a,b)    = (pk'          (c,a,b), pk'' (d,a,b))
>	pkmldl   lb ((c,d),a,b)    = (pkmldl'   lb (c,a,b)   , pkmldl''  lb (d,a,b))
>	pkmldr      ((c,d),a,b) rb = (pkmldr'      (c,a,b) rb, pkmldr''     (d,a,b) rb)
>	pkmldlr  lb ((c,d),a,b) rb = (pkmldlr'  lb (c,a,b) rb, pkmldlr''  lb (d,a,b) rb)
>	pkml	    ((c,d),a,b)    = (pkml'        (c,a,b)   , pkml'' (d,a,b))

>	pk2  e a (x,u) b (y,v) a' (z,w) b' d   = ((s1, s2), k1, l1)
>			      where (s1,k1,l1)=  pk2'  e a x b y a' z b' d
>				    (s2,_,_)  =  pk2'' e a u b v a' w b' d
>	kndl    lb ((a,b),c,d)    = (kndl'   lb (a,c,d)   , kndl'' lb (b,c,d))
>	kndr       ((a,b),c,d) rb = (kndr'      (a,c,d) rb, kndr''    (b,c,d) rb)
>	kndlr   lb ((a,b),c,d) rb = (kndlr'  lb (a,c,d) rb, kndlr'' lb (b,c,d) rb)

>	frd i      (c, d) rb = (frd' i     c rb, frd'' i    d rb)
>	bkd j  lb  (c, d)    = (bkd' j  lb c   , bkd'' j lb d   )   
>
>	scale lloc ((c,d),k,l) rloc = ((a,d),b)  
>				where (a,b) = scale' lloc (c,k,l) rloc
>				      (a2,b2) =scale'' lloc (d,k,l) rloc				    
>	unscale ((c,d),l) = (unscale' (c,l),unscale'' (d,l)) 			

>	emptymid k l (i,j)= [ (xs, xs2)| i   ==j] 
>				     where [xs]  = emptymid' k l (i,j)  
>				           [xs2] = emptymid'' k l (i,j)					      
>			    -- In this context xs is always a list containing only one element 
>	midbase  k l (i,j)= [ (xs, xs2)| i+1 ==j]
>				    where  [xs]  = midbase'  k l (i,j)
>				           [xs2] = midbase'' k l (i,j)		
>	middlro  k l (i,j)= [ (xs, xs2)| i+2 ==j]
>				     where [xs]  = middlro'  k l (i,j)
>				           [xs2] = middlro'' k l (i,j)		
>	middl    k   lb (c,d)	 = (middl'  k   lb c   , middl''  k   lb d)
>	middr      l 	(c,d) rb = (middr'    l    c rb, middr''    l    d rb)
>	middlr   k l lb (c,d) rb = (middlr' k l lb c rb, middlr'' k l lb d rb)
>	midregion (c,d) = (midregion'  c, midregion'' d)
>	pss  r	        = (pss'  r,pss'' r )


> (***) :: (Eq a, Eq b, Eq c, Eq d, Ord b , Ord a,Ord c, Ord d) => 
>		      (RNAInput -> FS_Algebra Int a b, RNAInput -> FS_AlgebraExt e a b) 
>				   -> (RNAInput -> FS_Algebra Int d c, RNAInput -> FS_AlgebraExt e d c)
>				   -> (RNAInput -> FS_Algebra Int (a,d) (b,c), RNAInput -> FS_AlgebraExt e (a,d) (b,c))
> a *** b = ((alg1 ***** alg2), (algext1 **** algext2) )
>			where (alg1, algext1) = a 
>			      (alg2, algext2) = b 
>

> skipleft:: a -> b -> b
> skipleft _ c   = c

> skipright:: a -> b -> a
> skipright c _ = c

> com3 :: (a -> c -> b -> e) -> (a -> d -> b -> f) -> a ->(c,d) -> b -> (e,f) 
> com3  f g a (c,d) b   = (f a c b, g a d b)

> compact:: [Component Ibase] -> [Component Ibase]
> compact [(SS (l,r))] | l == r    = []
>	     	       | otherwise = [SS (l,r)]
> compact xs         = xs    


> emin:: [(Int, Int, Int, Int ,Int)] ->[(Int, Int, Int, Int ,Int)] 
> emin []     = []
> emin (x:xs) = [emin_sub x xs]
>    where emin_sub m [] = m
>          emin_sub (l1,l2,e,x,y) ((l1',l2',e',x',y'):xs) | e <= e'   = emin_sub (l1,l2,e,x,y) xs
>							  | otherwise = emin_sub (l1',l2',e',x',y') xs


