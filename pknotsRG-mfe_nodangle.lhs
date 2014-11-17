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
>    edangle      =  --edl  <<< base +~~ closed ~~. loc  |||
>	             --edr  <<<  loc .~~ closed ~~+ base |||
>		     --edlr <<< base +~~ closed ~~+ base |||
>	             drem <<<          initstem        |||
>	      	     --kndr <<<          knot   ~~+ base |||
>		     --kndl <<< base +~~ knot 	       |||
>		     --kndlr<<< base +~~ knot   ~~+ base |||
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

>       multiloop = (--mldl  <<< base +~~ base ++~ base +++ ml_components          ~~+ base ~~+ base |||
>                    --mldr  <<< base +~~ base ++~ 	  ml_components ~~+ base ~~+ base ~~+ base |||
>                    --mldlr <<< base +~~ base ++~ base +++ ml_components ~~+ base ~~+ base ~~+ base |||
>                    ml    <<< base +~~ base ++~ 	  ml_components          ~~+ base ~~+ base) -- ... h
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
>		    --pkmldl  <<< base   +~~ knot		 ||| 
>		    --pkmldr  <<<		   knot ~~+ base |||
>		    --pkmldlr <<< base   +~~ knot ~~+ base |||
>		    pkml    <<<		   knot          ... h_l)    -- pk inside multiloop
>                   where

>	  dangle  = --dl   <<< base +~~  initstem ~~. loc  |||
>		    --dr   <<<  loc .~~  initstem ~~+ base |||
>		    --dlr  <<< base +~~  initstem ~~+ base |||
>	            drem <<<           initstem          ... h


>     knot      = tabulated ( pknot `with` pkmaxsize   ... h_p)
>	  where  
>	    pknot       (i,j) =  [pk' energy a u b v a' w b' (0,0) | l <- [i+3 .. j-8], k <- [l+4 .. j-4],
>   
>	        		        (alphanrg,h) <- p stacklen (i,k),
>                                       h >= 2, 
>                                       (betanrg, betalen)  <- p stacklen (l,j),
>                                       let h' = if (betalen + h) > (k-l) 
>                                                    then  k-l-h
>                                                    else betalen,
>                                       h' >= 2,                                                
>                                       a <- region   (i     , i+h  ),
>                                       u <- front'   (i+h+1,    l  ),  --replaces front j
>                                       b <- region   (l    , l+h'  ),
>                                       v <- middle (j-h') (i+h) (l+h', k-h  ),
>                                       a'<- region   (k-h  , k     ),
>                                       w <- back'    (k    , j-h'-2),  --replaces back i
>                                       b'<- region   (j-h' , j     ),
>                                       (correctionterm, _) <- p stacklen (l+h'-1,j-h'+1),               
>                                       let energy = alphanrg + betanrg - correctionterm
>                                       ]   

	    front j    =                 front'                |||
		         frd j	     <<< front' ~~+ base       ... h_l    -- one base dangling of b,b'

>           front'     = pul         <<< emptystrand           |||          
>		         	         comps		       ... h_l
>
>           middle k l = emptymid k l                          |||
>	       		 midbase k l	                       |||
>			 --middlro k l                           |||
>	                 --middl   k   <<< base +~~ mid          |||
>	                 --middr     l <<<          mid ~~+ base |||
>	                 --middlr  k l <<< base +~~ mid ~~+ base |||
>	                 midregion   <<<          mid          ... h_l
>           mid        = pul         <<< singlestrand          |||        
>		                         comps                 ... h_l
>	    

	    back i     =                back'		       |||   --  one base dangling of a,a'
			 bkd i       <<< base +~~ back'        ... h_l

>           back'      = pul         <<< emptystrand	       |||
>					 comps                 ... h_l

>	    singlestrand  = pss <<< region 
>	    emptystrand   = pss <<< uregion 

>   stacklen = tabulated(
>              (sum    <<<   base +~~ p stacklen                     ~~+ base)  `with` basepair  |||
>              (sumend <<<   base +~~ (region `with` (minloopsize 3)) ~~+ base)  `with` basepair  ...hmin)
>           where    sum      lb (c,k) rb   = (c + sr_energy inp (lb, rb), k+1)
>                    sumend   lb _ rb   = (0,1)
>   hmin []  = []
>   hmin xs = [minimum xs]


