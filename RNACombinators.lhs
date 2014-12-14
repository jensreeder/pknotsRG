 
           *******************************************
          *            RNACombinators                *
          *                                          *
          *     Basic combinators and variants       *
          *     tabulation and terminal parsers      *
          ********************************************


1. Operator priorities
2. Basic combinators
3. Combinator Variants
4. Tabulation
5. Terminal parsers
6. Utilities


> module RNACombinators where
> import Data.Array

1. Precedence of the combinators and infix declaration
------------------------------------------------------

> infix  8 <<<
> infixl 7 ~~~ , ~~ , ~~+, +~~, ~++, ++~,  ~-~, +++, .~~, ~~. , ++++, *~~, ~~*
> infixr 6 |||
> infix  5 ...

2. Basic Combinators
--------------------

A parser is a function that given a subword of the input, returns a list of all
its parses.

> type Parser b = Region -> [b]


A a region is a pair of subword boundaries. Region (i,j) of x holds
the elements x!(i+1) ... x!j.

> type Region = (Int,Int) 


The five fundamental combinators
--------------------------------

"Alt"-Combinator: Concatenation of result lists of alternative parses.

> (|||)           :: Parser b -> Parser b -> Parser b
> (|||) r q (i,j) = r (i,j) ++ q (i,j)


"Using" combinator: Directing parser results into evaluation function.

> (<<<)           :: (b -> c) -> Parser b -> Parser c
> (<<<) f q (i,j) =  map f (q (i,j))


"Next"-Combinator: Sequential composition of parsers.

> (~~~)           :: Parser (b -> c) -> Parser b -> Parser c
> (~~~) r q (i,j) =  [x y | k <- [i..j], x <- r (i,k), y <- q (k,j)]  


"Choice"-Combinator: Applying the choice function to parser results.

> (...)            :: Parser a -> ([a] -> [a]) -> Parser a
> (...) p pp (i,j) = pp (p (i,j))

"Axiom"-Combinator: Defines the result of a grammar

> axiom'           :: Int -> Parser a -> [a]
> axiom' n q	  =  q (0,n)



3. Combinator Variants
----------------------

"Using" Combinator for nullary operators

> (><<) f q (i,j) = [f | _ <- q(i,j)]

laxiom is an axiom variant used for testing and statistics.

> laxiom          :: Int -> Parser a -> [[a]]
> laxiom n q      =  [q (0,i) | i <- [0..n]]


Syntactic and semantic predicates
---------------------------------

"with" applies a filter to a region.

> with           :: Parser a -> ((Int,Int) -> Bool) -> Parser a
> with p f (i,j) = if f (i,j) then p (i,j)
>			      else []

"suchthat" applies a filter to parser results

> suchthat           :: Parser a -> (a -> Bool) -> Parser a
> suchthat p f (i,j) =  [z | z <- p (i,j), f z]


4. Tabulation
-------------

> type Parsetable a = Array Region [a]
> type Parsearray a = Array Int [a]

"table n p" records the results of parser p for all subwords of an input of size n.

 table     :: Int -> Parser a -> Parsetable a
 table n p =  array ((0,0),(n,n))
		    [((i,j),p (i,j)) | i<- [0..n], j<- [i..n]]

> table     :: Int -> Parser b -> Parser b
> table n p = lookup where
>   lookup (i,j) =  if i <= j then t!adr (i,j) else []
>   t            = array (0,(n+1)*(n+2) `div` 2)
>                       [(adr (i,j),p (i,j)) | i<- [0..n], j<- [i..n]]
>   adr (i,j)    = n*i - (i*(i-1)) `div` 2 + j

"p" is/was the table lookup function
(for backwards compatibility. The lookup is now implicit in the table.

> p = id

 p         :: Parsetable a -> Parser a
 p t (i,j) =  if i<= j then t!(i,j)
		        else []

A one-dimensional table is needed in some cases:
"table1 n p" records the results of parser for all suffixes of an input of size n.

> table1    :: Int -> Parser a -> Array Int [a]
> table1 n p = array (0,n) [(j,p (j,n)) | j <- [0..n]]

"q" is the array lookup function

> q         :: Parsearray a -> Parser  a
> q t (i,_) = t!i



Variants of the ~~~ Combinator
-----------------------------

Zero character on the lefthand (respectively righthand) side

> (.~~)           :: Parser (a -> b) -> Parser a -> Parser b
> (.~~) r p (i,j) = [x y | i < j, x <- r (i,i), y <- p (i,j)]

> (~~.)           :: Parser (a -> b) -> Parser a -> Parser b
> (~~.) p r (i,j) = [x y | i < j, x <- p (i,j), y <- r (j,j)]

Single character on the lefthand (respectively righthand) side

> (+~~)           :: Parser (a -> b) -> Parser a -> Parser b
> (+~~) r p (i,j) = [x y | i < j, x <- r (i,i+1), y <- p (i+1,j)]

> (~~+)           :: Parser (a -> b) -> Parser a -> Parser b
> (~~+) p r (i,j) = [x y | i < j, x <- p (i,j-1), y <- r (j-1,j)]

Two characters on the lefthand (respectively righthand) side

> (++~)           :: Parser (a -> b) -> Parser a -> Parser b
> (++~) r p (i,j) = [x y | i < j, x <- r (i,i+2), y <- p (i+2,j)]

> (~++)           :: Parser (a -> b) -> Parser a -> Parser b
> (~++) p r (i,j) = [x y | i < j, x <- p (i,j-2), y <- r (j-2,j)]

Three characters on the lefthand side

> (+++)           :: Parser (a -> b) -> Parser a -> Parser b
> (+++) r p (i,j) = [x y | i < j, x <- r (i,i+3), y <- p (i+3,j)]

Four characters on the lefthand side

> (++++)           :: Parser (a -> b) -> Parser a -> Parser b
> (++++) r p (i,j) = [x y | i < j, x <- r (i,i+4), y <- p (i+4,j)]

k characters on the lefthand side

> (*~~)           :: Int -> Parser (a -> b) -> Parser a -> Parser b
> (*~~) k r p (i,j) = [x y | i < j, x <- r (i,i+k), y <- p (i+k,j)]

k characters on the righthand side

> (~~*)           :: Int ->Parser (a -> b) -> Parser a -> Parser b
> (~~*) k r p (i,j) = [x y | k>0, i<j-k, x <- r (i,j-k), y <- p (j-k,j)]

up to k characters on the lefthand side

> (<~~)           :: Int -> Parser (a -> b) -> Parser a -> Parser b
> (<~~) k r p (i,j) = [x y | k'<-[0..k], i+k'<j, x <- r (i,i+k'), y <- p (i+k',j)]

up to k characters on the righthand side

> (~~<)  :: Int ->Parser (a -> b) -> Parser a -> Parser b
> (~~<) k r p (i,j) = [x y | k'<-[0..k], i < j-k', x <- r (i,j-k'), y <- p (j-k',j)]

Nonempty sequence on either side

> (~-~)           :: Parser (b -> c) -> Parser b -> Parser c
> (~-~) r q (i,j) = [f y | k <- [(i+1)..(j-1)], f <- r (i,k), y <- q (k,j)]  

Subwords on left and right of an explicit length range.

> (~~) :: (Int,Int) -> (Int,Int) -> Parser (a -> b) -> Parser a -> Parser b
> (~~) (l,u) (l',u') r q (i,j)
>      = [x y | k <- [max (i+l) (j-u') .. min (i+u) (j-l')],
>		x <- r (i,k), y <- q (k,j)]



5. Terminal parsers
-------------------
base parser recognizes a subword of lenght 1

> base ::  Parser Int 
> base    (i,j)   = [ j | (i+1) == j ]

loc returns its position, thus parses a subword of length 0

> loc :: Parser Int
> loc     (i,j)   = [ i | i == j ]

anyBase recognizes any subword of length 1 at position (i,j) and returns it.

> anyBase :: Array Int base -> Parser base
> anyBase inp (i,j) = [inp!j | i+1 == j]


The empty yield parser.

> empty      :: a -> Region -> [a]
> empty e (i,j) = [e | i==j]

region parses a nonempty region

> region       :: Parser (Int,Int)
> region (i,j) = [(i,j) | i < j]

uregion parses a possibly empty region

> uregion :: Parser (Int,Int)
> uregion (i,j) = [(i,j) | i <= j]

"get" recognizes a specific character x at position (i,j) and returns it.

> get             :: Eq base => Array Int base -> base -> Parser base
> get inp x (i,j) =  [x | i+1 == j, inp!j == x]


6. Utilities 
--------------------------------------

transform a list into an array

> mk :: [a] -> Array Int a
> mk xs = array (1,n) (zip [1..n] xs) where n = length xs

Return the length of a region.

> sizeof :: (Int,Int) -> Int
> sizeof (i,j) = j-i

Create an array and fill it with the list.

> toarray :: [b] -> Array Int b
> toarray l = array (1,length l) (zip [1..] l)

Tuple arguments

> combine  a b     = (a,b)
> combine3 a b c   = (a,b,c)
> combine4 a b c d = (a,b,c,d)
> fst' (a,b,c)     = a