\documentclass[leqno,fleqn,12pt]{article}

\usepackage{euler,beton,concrete,url,a4wide}
\usepackage[T1]{fontenc}

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt

%format * = "\mskip-4mu\times\mskip-4mu"
%format floor(x) = "\lfloor" x "\rfloor"
%format % = "/"
%format == = "=="
% comment format $ = "\ "

%options ghci -fglasgow-exts
\def\prompt#1{\noindent$\gg$ #1}

\title{On the Inexistence\\
       of a\\
       Unique Existential Binary Operator}
\author{
   Jo\~ao F. Ferreira \\{\tt\small joao@@joaoff.com}
}
\date{\today}

\begin{document}
\maketitle

\begin{abstract}
We prove that there is not any boolean binary operator that can be quantified over an 
arbitrary set of values to express that exactly one of them is $\sf{true}$. 
Our proof is a Haskell program that verifies this fact for all sixteen
possible boolean binary operators.
\end{abstract}

%if False

> module UEQ where

%endif

\section{Introduction}
Boolean inequality, usually denoted by $\not\equiv$ and sometimes called exclusive-or, can be used to express
that exactly one of two values is ${\sf true}$. However, we can not use it to express
that exactly one of three values is ${\sf true}$ (e.g. ${\sf true}{\not\equiv}{\sf true}{\not\equiv}{\sf true}$ is {\sf true} and all of the operands are {\sf true}). In this note, we prove that there
is not any binary operator that can be quantified over an arbitrary set of values to express that
exactly one of them is $\sf{true}$. Our proof is a Haskell program that, for all binary boolean operators $\oplus$, shows that it is impossible to evaluate $(a{\oplus}b){\oplus}c$ or $a{\oplus}(b{\oplus}c)$ to
{\sf true} exactly when one of $a$, $b$, and $c$ is {\sf true} and to {\sf false} otherwise.


\section{Boolean Binary Operators}
We start by defining some useful datatypes. A binary operator $\oplus$ has type |BinOp|;
it is represented as a list of pairs |(Input,Output)|, where |Input| is a pair of booleans 
$(a,b)$ and the |Output| is the result of $a{\oplus}b$.

> type Input   = (Bool,Bool)
> type Output  = Bool
> type BinOp   = [(Input,Output)]

The value |boolvars| is defined for convenience.

> boolvars  =  [True,False]

The function |inputs| lists all four possible inputs.

> inputs    :: [Input]
> inputs    =  [ (a,b) |  a <- boolvars, 
>                         b <- boolvars ]

The function |outputs| lists all sixteen possible outputs.

> outputs   :: [[Output]]
> outputs   =  [ [a,b,c,d] |  a <- boolvars, 
>                             b <- boolvars, 
>                             c <- boolvars, 
>                             d <- boolvars ]

The first element returned by |outputs| corresponds to the binary operator {\sl constant true},
as the following snippet shows:

\medskip
\indent\prompt{head outputs}\\
\indent\eval{head outputs}
\medskip

\noindent Finally, the function |operators| returns the list of all the sixteen boolean binary operators.

> operators  :: [BinOp]
> operators  = map (zip inputs) outputs

The first element returned by |operators| is the binary operator {\sl constant true}:

\medskip
\indent\prompt{head operators}\\
\indent\eval{head operators}
\medskip

\section{Unique Existential Operator}
Now, recall that our goal is to check the value of the two following expressions, for all
booleans $a$, $b$, and $c$, and for all boolean binary operators $\oplus$:

\[
(a{\oplus}b){\oplus}c {\textrm ~~~~and~~~~} a{\oplus}(b{\oplus}c) {\textrm ~~~.}
\]
First, we generate all possible inputs for the above expressions.

> tinps  :: [(Bool,Bool,Bool)]
> tinps  = [ (a,b,c) |  a <- boolvars,
>                       b <- boolvars,
>                       c <- boolvars ]

Second, we define two functions, |checkl| and |checkr|, that given a list of 
inputs and a binary operator, evaluates each of the inputs using that operator.
|checkl| associates to the left and |checkr| associates to the right.

> checkl                   :: [(Bool,Bool,Bool)] -> BinOp -> [Output]
> checkl []            _   = []
> checkl ((a,b,c):xs)  op  = checkop op ((checkop op (a,b)),c) : checkl xs op

> checkop               :: BinOp -> Input -> Bool
> checkop ((e,r):es) p  | e==p       = r
>                       | otherwise  = checkop es p

> checkr                   :: [(Bool,Bool,Bool)] -> BinOp -> [Output]
> checkr []            _   = []
> checkr ((a,b,c):xs)  op  = checkop op (a,(checkop op (b,c))) : checkr xs op

We can now evaluate all the possible outputs for the expression $(a{\oplus}b){\oplus}c$ by 
mapping the function |checkl tinps| over the list |operators|. Symmetrically, we can evaluate all
the possible outputs for the expression $a{\oplus}(b{\oplus}c)$ by mapping the function
|checkr tinps| over the list |operators|.

> expl  :: [[Output]]
> expl  = map (checkl tinps) operators

> expr  :: [[Output]]
> expr  = map (checkr tinps) operators

We now want to filter all the operators that have exactly three {\sf true} output entries.
We start by defining the function |fthree| that tests if a given list of outputs has exactly
three {\sf true} elements.

> fthree  :: [Output] -> Bool
> fthree  = (== 3) . length . filter (==True)

We then map |fthree| over |expl| and |expr|.

> tmp1 = map fthree expl
> tmp2 = map fthree expr

Now, using the next function, |flist|, we can combine the lists of booleans constructed
by |tmp1| and |tmp2| with the list |operators| to filter the operators we are interested in.

> flist  :: [Bool] -> [BinOp] -> [BinOp]
> flist  = (map snd .) . (filter fst .) . zip 

And so, the only operators that are of interest are:

> opl  :: [BinOp]
> opl  = flist tmp1 operators

> opr  :: [BinOp]
> opr  = flist tmp2 operators

For all the operators $\oplus$ in |opl|, we know that $(a{\oplus}b){\oplus}c$
returns exactly three {\sf true} values. Symmetrically, we also know that
for all the operators $\oplus$ in |opr|, $a{\oplus}(b{\oplus}c)$ returns
exactly three {\sf true} values. 

It remains to check if these three {\sf true}
values correspond to exactly when one of the arguments is {\sf true}.
We create a list with the three input combinations where exactly one
is {\sf true}.

> oneistrue = [(True,False,False),(False,True,False),(False,False,True)]

Finally, using the operators in |opl| and |opr|, we determine if these
inputs evaluate to {\sf true}.

> resultl  :: Bool
> resultl  = and $ map and $ map (checkl oneistrue) opl

> resultr  :: Bool
> resultr  = and $ map and $ map (checkr oneistrue) opr

As the following snippet shows, both |resultl| and |resultr| evaluate to {\sf false}. 
We can thus conclude that there is not any boolean binary operator that can be quantified over an 
arbitrary set of values to express that exactly one of them is $\sf{true}$. 

\medskip
\indent\prompt{resultl}\\
\indent\eval{resultl}\\
\indent\prompt{resultr}\\
\indent\eval{resultr}


\bibliographystyle{plain}
\bibliography{math,jff,bibliogr}
\end{document}
