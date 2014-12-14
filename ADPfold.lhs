	***************************************
	*	    ADPfold		      *	
	*				      *
      	*        A RNAfold clone              *
	*   O(n^3) time and O(n^2) space      *
	*    identical to RNAfold -noLP	      *
	*************************************** 

> module Main where

> import Data.Array
> import System.Environment(getArgs)
> import Foldingspace
> import RNACombinators
> import Energy
> import Algebras
> import Intloop

> main ::  IO()
> main  = do
>	  [arg1] <- getArgs
>	  let input	  = arg1
>             ereal:: Float
>             ereal       = (fromIntegral e / 100)	
>	      (e,p):xs    =  fold input (energy*** pp) in
>    	      putStr (input ++"\n"++ p ++ " ( " ++ show ereal ++")\n")

> fold :: [Char] ->(RNAInput -> FS_Algebra  Int a b
> 		      ,RNAInput -> FS_AlgebraExt  Int a b) -> [b] 

> fold sequence algebra = axiom (q struct) where
>
>   tabulated		= table  n
>   listed		= table1 n
>   n			= length sequence	
>   axiom		= axiom' n
>   inp			= mk (rna sequence)
>   basepair (i,j)      = basepair'  (inp,(i,j))
>   stackpair (i,j)     = stackpair' (inp,(i,j))
>   minloopsize m (i,j) = minloopsize'  m (inp,(i,j))
>   size:: Int -> Region -> Bool
>   size k (i,j)	= k == sizeof (i,j)


>   (alg, algext)       = algebra

>   (sadd,cadd,is,sr,hl,bl,br,il,ml,mldl,mldr,mldlr,dl,dr,dlr,edl,edr,edlr,
>	    drem, cons, ul, pul, addss, ssadd, nil, h, h_l, h_s, h_i, h_p) = alg inp

>   struct        = listed (
>	            sadd <<< base    +~~ q struct |||
>                   cadd <<< edangle ~~~ q struct |||
>                   empty nil ... h_s)
>              where   
>    edangle      =  edl  <<< base +~~ closed ~~. loc  |||
>	             edr  <<<  loc .~~ closed ~~+ base |||
>		     edlr <<< base +~~ closed ~~+ base |||
>	             drem <<<          initstem          ... h
>                where
>     initstem =  is <<< loc .~~ closed ~~. loc
>     closed      = tabulated (
>		    stack ||| (hairpin ||| leftB ||| rightB ||| iloop ||| multiloop) `with` stackpair ... h)
>                 where
>       stack     = (sr <<< base +~~ closed ~~+ base) `with` basepair
>       hairpin   = (hl <<< base +~~ base ++~ (region `with` (minloopsize 3)) ~~+ base ~~+ base)
>       leftB     = (bl <<< base +~~ base ++~ region ~~~ initstem             ~~+ base ~~+ base) ... h
>       rightB    = (br <<< base +~~ base ++~	         initstem ~~~ region  ~~+ base ~~+ base) ... h
>	iloop	  = (il	<<< base +~~ base ++~ region !~~ closed   ~~! region  ~~+ base ~~+ base) ... h where
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
>		    ul      <<<		   dangle   |||
>                   ssadd   <<< region ~~~ dangle   ... h_l)
>                   where

>	  dangle  = dl   <<< base +~~  initstem ~~. loc  |||
>		    dr   <<<  loc .~~  initstem ~~+ base |||
>		    dlr  <<< base +~~  initstem ~~+ base |||
>	            drem <<<           initstem          ... h
