	***************************************
	*	    pknotsRG-mfe       	      *	
	*				      *
      	*  Canonical RNA Structures including *
	*   pseudoknots in O(n^4) time and    *
	*             O(n^2) space.	      *
	*************************************** 

> module Main where

> import Array
> import System(getArgs)
> import Foldingspace
> import RNACombinators
> import Energy
> import Algebras

> main ::  IO()
> main  = do
>	  args <- getArgs
>	  let pkmaxsize  = case args of		 
>				[x] -> 0
>				[x,y] -> (read y)::Int
>				otherwise -> error "Error: pknotsRG-enf sequence [pkmaxsize]"
>	      input	 = head args		 
>             ((e,p):xs) = pknots input pkmaxsize (energy *** pp)
>             ereal      :: Float
>             ereal      = (fromIntegral e / 100) in
>    	      putStr (input ++"\n"++ p ++ " ( " ++ show ereal ++")\n")


> pknots :: [Char] -> Int -> ( (RNAInput -> FS_Algebra  Int a b)
> 		      ,(RNAInput -> FS_AlgebraExt  Int a b)) -> [b]

> pknots sequence maxpk algebra = axiom (q struct) where
>
>   tabulated		= table  n 
>   listed		= table1 n
>   n			= length sequence	
>   axiom		= axiom' n
>   inp			= mk (rna sequence)
>   basepair (i,j)      = basepair'  (inp,(i,j))
>   stackpair (i,j)     = stackpair' (inp,(i,j))
>   minloopsize m (i,j) = minloopsize'  m (inp,(i,j))
>   pkmaxsize 
>	    | maxpk == 0  = \t -> True
>	    | otherwise   = maxsize maxpk
>   (alg, algext)       = algebra
>
>   (sadd,cadd,is,sr,hl,bl,br,il,
>	    ml, mldl, mldr, mldlr, dl, dr, dlr, edl, edr, edlr,
>	    drem, cons, ul, pul, addss, ssadd, nil, h, h_l, h_s, h_i, h_p) = alg inp
>   (pk, pkmldl, pkmldr, pkmldlr, pkml, pk',
>	    kndl, kndr,  kndlr, frd, bkd, scale, unscale, 
>	    emptymid, midbase, middlro, middl, middr, middlr, midregion, pss)= algext inp
>
>   struct        = listed (
>	            sadd <<< base    +~~ q struct |||
>                   cadd <<< edangle ~~~ q struct |||
>                   empty nil ... h_s)
>              where   
>    edangle      =  edl  <<< base +~~ closed ~~. loc  |||
>	             edr  <<<  loc .~~ closed ~~+ base |||
>		     edlr <<< base +~~ closed ~~+ base |||
>	             drem <<<          initstem        |||
>	      	     kndr <<<          knot   ~~+ base |||
>		     kndl <<< base +~~ knot 	       |||
>		     kndlr<<< base +~~ knot   ~~+ base |||
>		     pk   <<<	       knot	 	 ... h
>                where

>     initstem =  is <<< loc .~~ closed ~~. loc
>   
>     closed      = tabulated (
>		    stack   ||| (hairpin ||| leftB  ||| rightB ||| iloop ||| multiloop) `with` stackpair ... h)
>                 where
>       stack     = (sr <<< base +~~ closed ~~+ base)  `with` basepair
>       hairpin   = (hl <<< base +~~ base ++~ (region `with` (minloopsize 3)) ~~+ base ~~+ base)
>       leftB     = (bl <<< base +~~ base ++~ region ~~~ initstem             ~~+ base ~~+ base) ... h
>       rightB    = (br <<< base +~~ base ++~	         initstem ~~~ region  ~~+ base ~~+ base) ... h
>	iloop	  = (il	<<< base +~~ base ++~ region !~~ closed   ~~! region  ~~+ base ~~+ base) ... h
>		    where
>			      infixl 7 ~~!,!~~
>			      (~~!) = (~~<) 30
>			      (!~~) = (<~~) 32 

>       multiloop = (mldl  <<< base +~~ base ++~ base +++ ml_components          ~~+ base ~~+ base |||
>                    mldr  <<< base +~~ base ++~ 	  ml_components ~~+ base ~~+ base ~~+ base |||
>                    mldlr <<< base +~~ base ++~ base +++ ml_components ~~+ base ~~+ base ~~+ base |||
>                    ml    <<< base +~~ base ++~ 	  ml_components          ~~+ base ~~+ base) ... h
>                    where
>         ml_components = combine <<< block ~~~ comps    
                   
>     comps     = tabulated (
>		    cons  <<< block ~~~ comps  |||
>                             block            |||
>                   addss <<< block ~~~ region ... h_l)
>
>     block     = tabulated (
>		    ul      <<<		   dangle        |||
>                   ssadd   <<< region ~~~ dangle	 |||
>		    pkmldl  <<< base   +~~ knot		 ||| 
>		    pkmldr  <<<		   knot ~~+ base |||
>		    pkmldlr <<< base   +~~ knot ~~+ base |||
>		    pkml    <<<		   knot          ... h_l)    -- pk inside multiloop
>                   where

>	  dangle  = dl   <<< base +~~  initstem ~~. loc  |||
>		    dr   <<<  loc .~~  initstem ~~+ base |||
>		    dlr  <<< base +~~  initstem ~~+ base |||
>	            drem <<<           initstem          ... h


>     knot      = tabulated ( pknot `with` pkmaxsize   ... h_p)
>	  where  
>	    pknot       (i,j) = [pk' energy a u b v a' w b' dangle| l <- [i+3 .. j-8], k <- [l+4 .. j-4], 
			
	    The helices a and b should not overlap each other and not exceed [l...k].
	    Furthermore each helix must have a minimum length of two bases. Due to
	    stereochemical reasons one base in the front part and two bases in the back
	    part are left explicitely unpaired. These bases should brigde the stacks.
	    With these considerations we can fix the bounds for k and l.
	    
>				        (alpha,alpha', alphanrg,x1,y1) <- (stack' (i,k) ++ stack (i,k)), 
>					(beta, beta' , betanrg ,x2,y2) <- (getbeta (l,j, k-alpha')),
>				            a <- region     (i   , i+alpha  ),
>					    u <- front  j   (i+alpha+1,  l  ),
>					    b <- region     (l   , l+beta   ),
>					    v <- middle (j-beta') (i+alpha) (l+beta, k-alpha'),
>					    a'<- region     (k-alpha', k    ),
>				            w <- back   i   (k   , j-beta'-2),
>					    b'<- region     (j-beta', j     ),
>					    dangle <- [(max x1 y1, max x2 y2)],
>				            energy <- [alphanrg + betanrg
>						       + npp * fromIntegral(abs(alpha-alpha') + abs(beta-beta'))]
>				      	    ]
>	    front j    =                 front'                |||
>		         frd j	     <<< front' ~~+ base       ... h_l    -- one base dangling of b,b'
>           front'     = pul         <<< emptystrand           |||          
>		         	         comps		       ... h_l
>
>           middle k l = emptymid k l                          |||
>	       		 midbase k l	                       |||
>			 middlro k l                           |||
>	                 middl   k   <<< base +~~ mid          |||
>	                 middr     l <<<          mid ~~+ base |||
>	                 middlr  k l <<< base +~~ mid ~~+ base |||
>	                 midregion   <<<          mid          ... h_l
>           mid        = pul         <<< singlestrand          |||        
>		                         comps                 ... h_l
>	    
>	    back i     =                back'		       |||   --  one base dangling of a,a'
>			 bkd i       <<< base +~~ back'        ... h_l
>           back'      = pul         <<< emptystrand	       |||
>					 comps                 ... h_l

>	    singlestrand  = pss <<< region 
>	    emptystrand   = pss <<< uregion 

    'stack' records the maximal helix of a (hypothetical) stem
    starting at position i and ending at j.  Only canonical helices are found.
    stack contains a 1-nt bulge stack' not.
    The result of the parsers is a list of 5-tuples:
    (length of helix starting at i, lenght of helix ending at j, MFE,pos of bulge, pos of bulge)
    Unfortunately the nonterminal stack is used also in a local definition of closed above. 

>   stack = tabulated (
>		(countbp <<< base +~~                   stack           ~~+ base ) `with` basepair  |||
>	        (countbl <<< base +~~ base ++~ base +++ stack' ~~+ base ~~+ base ) `with` stackpair |||
>		(countbr <<< base +~~ base ++~ stack' ~~+ base ~~+ base ~~+ base ) `with` stackpair ... emin )
>   stack' = tabulated(
>		(countbp <<< base +~~           stack'                         ~~+ base   	 ) `with` basepair  |||
>               (count2  <<< base +~~ base ++~ (region `with` (minloopsize 3)) ~~+ base ~~+ base ) `with` stackpair ... emin)
>

   getbeta chooses the length of the second helix. If the helices overlap we have to
   take care were this overlap happens.

>   getbeta (l, j, alphaend) = [ tup | tup <- help (stack' (l,j)) ++ help (stack (l,j))] 
>      where help []		     = []
>	     help [(b,b',nrg,x,y)] 
>               | newb < 2                 = []
>		| l+b <= alphaend          = [(b,b',nrg,x,y)]  --no overlap
>                                     -- overlap, without bulges
>	        | x==0 && y==0             = [(newb ,newb, nrg - head(stacknrg (l+newb-1, j-newb+1)),x,y)]
>				      -- bulge in overlap
>		| x==0 && y<=j-newb        = [(newb, newb, nrg - head(stack_wb (l+newb-1, j-newb+1)),x,0)]
>				      -- bulge not in overlap
>	        | x==0 && y>j-newb         = [(newb, newb+1,nrg-  head(stacknrg (l+newb-1, j-newb)), x,y)]
>				      -- bulge in overlap
>		| x > alphaend             = [(newb, newb, nrg -  head(stack_wb (l+newb-1, j-newb+1)),0,y)]
>				      -- bulge adjacent to end of alpha
>	        | x == alphaend            = [(newb-1, newb-1,nrg - head (stack_wb (x-2,j-newb+2))   ,0,y)]
>		         	      -- bulge not in overlap
>      	        | x < alphaend             = [(newb, newb-1,nrg- head (stacknrg (l+newb-1, j-newb+2)),x,y)]
>			     	      -- this case should never occur
>               | otherwise                = error ("no rule to score pseudoknot") 
>		     where newb            = alphaend-l

    this table stores the energy of a helix of maximal length without bulge --

>   stacknrg = tabulated(
>		(sum    <<<   base +~~ stacknrg                      ~~+ base)  `with` basepair  |||
>		(sumend <<<   base +~~ (region `with` (minloopsize 3)) ~~+ base)  `with` basepair  ...hmin)
>           where    sum      lb c rb   = c + sr_energy inp (lb, rb) 
>		     sumend   lb _ rb   = 0 

    this table stores the energy of stacks that may start with a bulge (noncanonical stack)
    We need this as a correctionterm in case of overlapping pseudoknotstems

>   stack_wb = tabulated(
>		 bulgel  <<<          base +~~ stacknrg ~~. loc           |||
>	         bulger  <<<          loc  .~~ stacknrg ~~+ base          |||
>               (stack2  <<<          base +~~ stack_wb ~~+ base) `with` basepair  ...hmin)

   Functions for all algebras necessary for 
   the computation of the max stem length/energy

>   countbp     lb    (c,c',e,x,y)    rb      = (c+1, c'+1, e+sr_energy inp (lb, rb),x,y )
>   count2      lb _  _  _  rb                = (2, 2, sr_energy inp (lb, rb), 0, 0)	
>   countbl llb lb bl (c,c',e,x,y)    rb rrb  = (c+3, c'+2, e+sr_energy inp (llb, rrb)
>					        +  bl_energy inp lb (bl-1,bl) rb, bl ,y)
>   countbr llb lb    (c,c',e,x,y) br rb rrb  = (c+2, c'+3, e+sr_energy inp (llb, rrb)
>					        +  br_energy inp lb (br-1,br) rb,y,br) 
   
>   bulgel bl e rloc = e   + bl_energy inp (bl-1) (bl-1, bl) (rloc+1)
>   bulger lloc e br = e   + br_energy inp (lloc ) (br-1,br) (br+1)
>   stack2  lb e rb  = e + sr_energy inp (lb-1, rb+1)
>
>   hmin []  = []
>   hmin xs = [minimum xs]