---
title: "Budge interpreter in Haskell"
author: "Boro Sitnikovski"
---

```
This is a literate Haskell file. You can build an HTML with pandoc by running `pandoc -s budge.lhs -o budge.html` or run it with stack with `stack repl budge.lhs`.
```

Budge interpreter in Haskell
============================

Since sequences can either contain a number or a sequence, we encode that in our data type:

> import qualified Data.Map as M
> data Budge = BNum Int | BSeq Int [Budge]
>
> instance Show Budge where
>   show (BNum x) = show x
>   show (BSeq x xs) = "[" ++ show x ++ "," ++ tail (show xs)

With the following helper functions for getting prime numbers:

> p :: Int -> Integer
> p x = primes !! (x - 1)
>   where
>   primes = 2 : filter isPrime [3,5..]
>   isPrime n = all (\p -> n `mod` p /= 0) . takeWhile (\p -> p^2 <= n) $ primes

Now we can implement the interpreter as follows:

> evaluate :: Integer -> [Budge] -> Integer
> evaluate i ((BNum x):xs) | signum x == 1  =
>   evaluate (i * p x) xs
> evaluate i ((BNum x):xs) | signum x == -1 =
>   if i `rem` p (abs x) == 0
>   then evaluate (i `div` p (abs x)) xs
>   else evaluate i xs
> evaluate i l@((BSeq x' x):xs) =
>   if i `rem` p (abs x') == 0
>   then evaluate (evaluate i x) l
>   else evaluate i xs
> evaluate i [] = i

Use these helper methods to convert between a number and a list of registers (prime factorization):

> getRegisters :: Integer -> [(Int, Int)]
> getRegisters i = M.toList $ M.fromListWith (+) $ go [] i 1
>   where
>   go acc 1 _ = acc
>   go acc i n | i `rem` p n == 0 = go ((n, 1) : acc) (i `div` p n) n
>   go acc i n = go acc i (n + 1)
>
> setRegisters :: [(Int, Int)] -> Integer
> setRegisters ((a, b):xs) = p a ^ b * setRegisters xs
> setRegisters [] = 1

Example usage:

> egReg1 = getRegisters 12345 -- outputs `[(3,1),(5,1),(823,1)]`
> egReg2 = setRegisters $ getRegisters 12345 -- outputs `12345`

Examples
========

For example, to set register 1 to value 4, use the first prime $p(1) = 2$ and then power it to the value, i.e. $2^4$. To also set the second register to another value, say 5, use the second prime $p(2) = 3$ and power it to the value $3^5$. Multiply both registers like so to represent the value (4, 5) in memory: $2^4 \cdot 3^5$.

Then, to apply the code `[[2, -2, 1]]` to that input, use something like:

> egEval = evaluate (2^4 * 3^5) [BSeq 2 [BNum (-2), BNum 1]]

The prime factorization of 512 is $2^9$, which indicates that the first register ($p(1) = 2$) has a value of 9, i.e. the addition of 4 and 5.

Or, easier with the helper methods:

> egEval' = getRegisters $ evaluate (setRegisters [(1, 4), (2, 5)]) [BSeq 2 [BNum (-2), BNum 1]]

Efficiency
==========

A more efficient interpreter would be to use a `Map` for registers and directly adjust the values there, rather than relying on number division:

> fastEvaluate' :: M.Map Int Int -> [Budge] -> M.Map Int Int
> fastEvaluate' i ((BNum x):xs) =
>   let key   = abs x
>       value = M.findWithDefault 0 (abs x) i in
>       fastEvaluate' (M.insert key (max 0 (value + signum x)) i) xs
> fastEvaluate' i l@((BSeq x' x):xs) =
>   if M.findWithDefault 0 (abs x') i /= 0
>   then fastEvaluate' (fastEvaluate' i x) l
>   else fastEvaluate' i xs
> fastEvaluate' i [] = i
> fastEvaluate i l = M.toList $ M.filter (/= 0) (fastEvaluate' (M.fromList i) l)

The same example as before, using the `fastEvaluate` function:

> egEval'' = fastEvaluate [(1, 4), (2, 5)] [BSeq 2 [BNum (-2), BNum 1]]

Arithmetic
----------

Addition
--------

*Input*: $2^x \cdot 3^y$. *Output*: $2^n$.

The following code adds $x$ and $y$.

> arithAdd = [BSeq 2 [BNum (-2), BNum 1]]

> egAdd = fastEvaluate [(1, 3), (2, 3)] arithAdd

Subtraction
-----------

*Input*: $2^x \cdot 3^y$. *Output*: $2^n \cdot 3^k$.

The following code will set $k$ to 1 if $y \leq x$, and 0 otherwise. The final result is stored in $n$.

> arithSub = [
>   BSeq 1 [BNum (-1), BNum 3, BNum 5], -- move r1 to r3 r4
>   BSeq 2 [BNum (-2), BNum 4, BNum 6], -- move r2 to r5 r6
>   BSeq 3 [BNum (-3), BNum (-4)],   -- calculate r3 - r4
>   BSeq 6 [BNum (-5), BNum (-6)],   -- calculate r6 - r5
>   BSeq 4 [BNum (-4), BNum 1, BNum 3], -- move r4 to r1 and r3 (if it was set)
>   BSeq 3 [BSeq 3 [BNum (-3)], BNum 2],   -- if r3 was set, then set r2 to 1 to indicate flag
>   BSeq 5 [BNum (-5), BNum 1]]      -- move r5 to r1 (if it was set)

> egSub1 = fastEvaluate [(1, 5), (2, 3)] arithSub
> egSub2 = fastEvaluate [(1, 3), (2, 5)] arithSub

Multiplication
--------------

*Input*: $2^x \cdot 3^y$. *Output*: $2^n$.

This code sets $n$ to $x \cdot y$.

> arithMul = [
>   BSeq 1 [BNum (-1), BSeq 2 [BNum (-2), BNum 3, BNum 4], BSeq 4 [BNum (-4), BNum 2]],
>   BSeq 2 [BNum (-2)],
>   BSeq 3 [BNum (-3), BNum 1]]

> egMul = fastEvaluate [(1, 2), (2, 4)] arithMul

Division
--------

*Input*: $2^x \cdot 3^y$. *Output*: $2^n \cdot 3^k$.

The following code only works when $x \geq y$. Given $a = qb + r$ where $a$ is input through $x$ and $b$ is input through $y$, it will calculate $q$ into $n$ and $r$ into $k$.

> arithDiv = [
>   BNum 9,
>   BSeq 9 -- while x>y
>     -- save r2
>     ([BSeq 2 [BNum (-2), BNum 7, BNum 8],
>     BSeq 8 [BNum (-8), BNum 2]]
>     ++ arithSub ++ -- see "Composing code"
>     -- negate r2 (see logical gate "Not")
>     [BNum 3, BSeq 2 [BNum (-2), BNum (-3)], BSeq 3 [BNum (-3), BNum 2],
>     -- store r2 to r9
>     BSeq 9 [BNum (-9)], BSeq 2 [BNum (-2), BNum 9],
>     -- bring back r2
>     BSeq 7 [BNum (-7), BNum 2],
>     BNum 10 -- increase quotient
>   ]),
>   BSeq 1 [BNum (-1), BNum (-2)], -- calc remainder (r2>r1 from last sub)
>   BSeq 10 [BNum (-10), BNum 1], BNum (-1)] -- set r1=r10 (quotient)

The idea is to keep subtracting until subtraction returns 1 in $r_2$ (second register), which means underflow. We negate $r_2$ because Budge loops only work with >1 checks. We keep track of the number of subtractions and then set $r_2 = r_2 - r_1$ for the remainder.

> egDiv1 = fastEvaluate [(1, 4), (2, 2)] arithDiv
> egDiv2 = fastEvaluate [(1, 4), (2, 3)] arithDiv

Exponents
---------

*Input*: $2^x \cdot 3^y$. *Output*: $2^n$.

This code sets $n$ to $x^y$. Requires $y>0$.

> arithExp = [
>   BNum (-2),
>   BSeq 2 [BNum (-2), BNum 5],         -- move r2 to r5
>   BSeq 1 [BNum (-1), BNum 6, BNum 7], -- set r6, r7 to r1
>   BSeq 7 [BNum (-7), BNum 1],         -- move r7 to r1
>   BSeq 5 ([BNum (-5),                 -- while y>0
>     BSeq 6 [BNum (-6), BNum 7, BNum 2], -- set r7, r2 to r6
>     BSeq 7 [BNum (-7), BNum 6]]         -- bring r6 back
>     ++ arithMul),              -- multiply
>   BSeq 6 [BNum (-6)]]          -- flush r6

> egExp = fastEvaluate [(1, 2), (2, 3)] arithExp

Logic gates
-----------

> logicNot = [BNum 2, BSeq 1 [BNum (-1), BNum (-2)], BSeq 2 [BNum (-2), BNum 1]]
> logicAnd = [BSeq 1 [BNum (-1), BNum 3], BSeq 2 [BNum (-2), BNum 3], BNum (-3), BSeq 3 [BNum (-3), BNum 1]]
> logicOr  = [BSeq 1 [BNum (-1), BNum (-2), BNum 3], BSeq 2 [BNum (-2), BNum 3], BSeq 3 [BNum (-3), BNum 1]]

> egNot  = [ (i, fastEvaluate [(1, i)] logicNot) | i <- [0..2]]
> egAnd  = [ (i, j, fastEvaluate [(1, i), (2, j)] logicAnd) | i <- [0..1], j <- [0..1]]
> egOr   = [ (i, j, fastEvaluate [(1, i), (2, j)] logicOr) | i <- [0..1], j <- [0..1]]

Misc. algorithms
----------------

Composing code
--------------

*Input*: $2^x \cdot 3^y$. *Output*: $2^n$.

The Nand gate can be implemented by composing the `logicAnd` and then the `logicNot` gate.

For example, in the following code, we simply merge the two lists:

> logicNand = logicAnd ++ logicNot

> egNand = [ (i, j, fastEvaluate [(1, i), (2, j)] logicNand) | i <- [0..1], j <- [0..1]]

When composing code make sure you have made a copy of all the affected registers (if needed) since if there are overlapping registers some of the data may be overwritten.

Fibonacci
---------

*Input*: $2^x$. *Output*: $2^n$.

The following program sets $n$ to $Fib(x)$.

> fib = [
>   BNum 3,    -- r1 = input/output, r2 = 0, r3 = 1, r4 = 0, r5 = 0
>   BSeq 1     -- while n > 1
>     ([BNum (-1),                     -- decrease n
>       BSeq 3 [BNum (-3), BNum 2, BNum 4], -- move r3 to r4, and add it to r2
>       BSeq 2 [BNum (-2), BNum 5],      -- move r2 to r5
>       BSeq 4 [BNum (-4), BNum 2],      -- move r4 to r2, and add it to r2
>       BSeq 5 [BNum (-5), BNum 3]]),    -- move r5 to r3
>   BSeq 3 [BNum (-3)],      -- flush r3
>   BSeq 2 [BNum (-2), BNum 1]] -- move r2 to r1

> egFib = [ (i, fastEvaluate [(1, i)] fib) | i <- [0..6] ]

GCD
---

*Input*: $2^x \cdot 3^y$. *Output*: $2^n$.

Sets $n$ to $GCD(x, y)$.

> gcd' = [
>   BSeq 2
>     ([BSeq 2 [BNum (-2), BNum 11, BNum 12], -- copy b=r2 to r11, r12
>     BSeq 12 [BNum (-12), BNum 2]]       -- bring back b
>     ++ arithDiv ++
>     [BSeq 1 [BNum (-1)], BSeq 11 [BNum (-11), BNum 1]])] -- set a = b
>     -- b is already remainder

> egGcd1 = fastEvaluate [(1, 2), (2, 4)] gcd'
> egGcd2 = fastEvaluate [(1, 3), (2, 5)] gcd'
> egGcd3 = fastEvaluate [(1, 12), (2, 16)] gcd'

Primality test
--------------

*Input*: $2^x$. *Output*: $2^n$.

Sets $n$ to 1 if $x$ is prime, and 0 otherwise. Requires $x>1$.

> isPrime = [
>   BSeq 1 [BNum (-1), BNum 11, BNum 12],    -- copy r1 to r11/r12
>   BSeq 11
>     ([BSeq 1 [BNum (-1)],
>     BSeq 12 [BNum (-12), BNum 1, BNum 15], -- first argument is original input
>     BSeq 15 [BNum (-15), BNum 12],      -- save original value from r15 (tmp) to r12
>     BSeq 2 [BNum (-2)],
>     BSeq 11 [BNum (-11), BNum 15],      -- copy r11 to r15
>     BSeq 15 [BNum (-15), BNum 2, BNum 11]] -- second argument is current iterator
>     ++ arithDiv ++                -- do the division
>     [
>     -- negate r2 (see logical gate "Not")
>     BSeq 3 [BNum (-3)], BNum 3, BSeq 2 [BNum (-2), BNum (-3)], BSeq 3 [BNum (-3), BNum 2],
>     -- if there was a non-zero remainder, it is now zero
>     BSeq 2 [BNum (-2), BNum 14],      -- if the remainder was zero, then it will be one and added to 14
>     BNum (-11)
>   ]),
>   BSeq 12 [BNum (-12)],                       -- flush r12 (original input)
>   BSeq 1 [BNum (-1)], BSeq 14 [BNum (-14), BNum 1], -- move result to r1
>   -- at this point, r1 contains the number of factors
>   -- if it's a prime, the number of factors will be two.
>   BNum (-1), BNum (-1)                  ,        -- if prime, r1 = 0, else r1 > 1
>   -- negate r1 for final result
>   BSeq 2 [BNum (-2)], BNum 2, BSeq 1 [BNum (-1), BNum (-2)], BSeq 2 [BNum (-2), BNum 1]]

The idea is to store in $r_{12}$ the result of `!(n%i)` for `i=n;i>=0`. We say that a number is prime if $r_{12}=2$`, i.e. only two numbers divide the number (1 and itself).

> egPrime = [ (i, fastEvaluate [(1, i)] isPrime) | i <- [2..9] ]

Logarithm
---------

*Input*: $2^x \cdot 3^y$. *Output*: $2^n$.

Sets $n$ to $log_y(x)$.

> logn = [
>   BSeq 2 [BNum (-2), BNum 12], -- store r2 to r12
>   BSeq 1 -- while the first argument is non-zero
>     ([BSeq 2 [BNum (-2)],             -- flush r2
>     BSeq 15 [BNum (-15)],            -- flush r15
>     BSeq 12 [BNum (-12), BNum 2, BNum 15], -- restore r2 and save it to r3
>     BSeq 15 [BNum (-15), BNum 12]]      -- restore r12
>     ++ arithDiv ++                -- divide r1 by r2
>     -- negate r2 (see logical gate "Not")
>     [BSeq 3 [BNum (-3)], BNum 3, BSeq 2 [BNum (-2), BNum (-3)], BSeq 3 [BNum (-3), BNum 2],
>     BNum 11]),                       -- increase division count
>     BNum (-11), -- no off by one error
>     BSeq 11 [BNum (-11), BNum 1], -- flush r11 and move to r1
>     BSeq 12 [BNum (-12)]]      -- flush r12

> egLog2 = [ (i, fastEvaluate [(1, i), (2, 2)] logn) | i <- [2..8] ]
> egLog3 = [ (i, fastEvaluate [(1, i), (2, 3)] logn) | i <- [3..9] ]

Representing sequences
----------------------

As an example, the sequence $(1, 2, 3)$ can be represented with the number $2^1 \cdot 3^2 \cdot 5^3 = 2250$, using Gödel numbering. We can store this number in the first register, thus $i = 2^{2250}$. To retrieve $2250$ from $2^{2250}$, we use the logarithm code. Further, to retrieve the $n$-th element of the sequence, we keep dividing $2250$ by $p(n)$ until there's no remainder, and count the divisions. For example, to get the second element, $p(2) = 3$ thus $2250/3 = 750$ is one division, and $750/3$ is another division (note that $250/3$ is not divisible) - so two divisions in total which represent the value of the index.
