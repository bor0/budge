---
title: "Budge-PL interpreter in Haskell"
author: "Boro Sitnikovski"
---

```
This is a literate Haskell file. You can build an HTML with pandoc by running `pandoc -s budge.lhs -o budge.html` or run it with stack with `stack repl budge.lhs`.
```

Budge-PL interpreter in Haskell
===============================

Since sequences can either contain a number or a sequence, we encode that in our data type:

> -- data BudgeCmd = CNum Int | CCons BudgeCmd BudgeCmd | CSeq Int BudgeCmd

However, a data type that uses lists directly would make it easier to represent programs.

> import qualified Data.Map as M
> data BudgeCmd = CNum Int | CWhile Int [BudgeCmd]
>
> instance Show BudgeCmd where
>   show (CNum x) = show x
>   show (CWhile x xs) = "[" ++ show x ++ "," ++ tail (show xs)

With the following helper functions for getting prime numbers:

> p :: Int -> Integer
> p x = primes !! (x - 1)
>   where
>   primes = 2 : filter isPrime [3,5..]
>   isPrime n = all (\p -> n `mod` p /= 0) . takeWhile (\p -> p^2 <= n) $ primes

Now we can implement the interpreter as follows:

> evaluate :: Integer -> [BudgeCmd] -> Integer
> evaluate i ((CNum x):xs) | signum x == 1  =
>   evaluate (i * p x) xs
> evaluate i ((CNum x):xs) | signum x == -1 =
>   if i `rem` p (abs x) == 0
>   then evaluate (i `div` p (abs x)) xs
>   else evaluate i xs
> evaluate i l@((CWhile x' x):xs) =
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

> egEval = evaluate (2^4 * 3^5) [CWhile 2 [CNum (-2), CNum 1]]

The prime factorization of 512 is $2^9$, which indicates that the first register ($p(1) = 2$) has a value of 9, i.e. the addition of 4 and 5.

Or, easier with the helper methods:

> egEval' = getRegisters $ evaluate (setRegisters [(1, 4), (2, 5)]) [CWhile 2 [CNum (-2), CNum 1]]

Efficiency
==========

A more efficient interpreter would be to use a `Map` for registers and directly adjust the values there, rather than relying on number division:

> fastEvaluate' :: M.Map Int Int -> [BudgeCmd] -> M.Map Int Int
> fastEvaluate' i ((CNum x):xs) =
>   let key   = abs x
>       value = M.findWithDefault 0 (abs x) i in
>       fastEvaluate' (M.insert key (max 0 (value + signum x)) i) xs
> fastEvaluate' i l@((CWhile x' x):xs) =
>   if M.findWithDefault 0 (abs x') i /= 0
>   then fastEvaluate' (fastEvaluate' i x) l
>   else fastEvaluate' i xs
> fastEvaluate' i [] = i
> fastEvaluate i l = M.toList $ M.filter (/= 0) (fastEvaluate' (M.fromList i) l)

The same example as before, using the `fastEvaluate` function:

> egEval'' = fastEvaluate [(1, 4), (2, 5)] [CWhile 2 [CNum (-2), CNum 1]]

Arithmetic
----------

Addition
--------

*Input*: $2^x \cdot 3^y$. *Output*: $2^n$.

The following code adds $x$ and $y$.

> arithAdd = [CWhile 2 [CNum (-2), CNum 1]]

> egAdd = fastEvaluate [(1, 3), (2, 3)] arithAdd

Subtraction
-----------

*Input*: $2^x \cdot 3^y$. *Output*: $2^n \cdot 3^k$.

The following code will set $k$ to 1 if $y > x$, and 0 otherwise. The final result is $n = |x - y|$.

> arithSub = [
>   CWhile 1 [CNum (-1), CNum 3, CNum 5], -- move r1 to r3 r4
>   CWhile 2 [CNum (-2), CNum 4, CNum 6], -- move r2 to r5 r6
>   CWhile 3 [CNum (-3), CNum (-4)],      -- calculate r3 - r4
>   CWhile 6 [CNum (-5), CNum (-6)],      -- calculate r6 - r5
>   CWhile 4 [CNum (-4), CNum 1, CNum 3],      -- case x > y: move r4 to r1 and r3 (if it was set)
>   CWhile 3 [CWhile 3 [CNum (-3)], CNum 2],   -- if r3 was set, then set r2 to 1 to indicate flag
>   CWhile 5 [CNum (-5), CNum 1]]         -- otherwise case y >= x: move r5 to r1 (if it was set)

> egSub1 = fastEvaluate [(1, 5), (2, 3)] arithSub
> egSub2 = fastEvaluate [(1, 3), (2, 5)] arithSub

Multiplication
--------------

*Input*: $2^x \cdot 3^y$. *Output*: $2^n$.

This code sets $n$ to $x \cdot y$.

> arithMul = [
>   CWhile 1 [CNum (-1), CWhile 2 [CNum (-2), CNum 3, CNum 4], CWhile 4 [CNum (-4), CNum 2]],
>   CWhile 2 [CNum (-2)],
>   CWhile 3 [CNum (-3), CNum 1]]

> egMul = fastEvaluate [(1, 2), (2, 4)] arithMul

Division
--------

*Input*: $2^x \cdot 3^y$. *Output*: $2^n \cdot 3^k$.

Given $a = qb + r$ where $a$ is input through $x$ and $b$ is input through $y$, it will calculate $q$ into $n$ and $r$ into $k$.

> arithDiv = [
>   CWhile 2 [CNum (-2), CNum 7], -- store r2 in r7
>   CWhile 1 -- while r1>0
>     ([CWhile 7 [CNum (-7), CNum 2, CNum 8], -- bring back r2
>     CWhile 8 [CNum (-8), CNum 7]]           -- save r2 to r7
>     ++ arithSub ++                          -- see "Composing code"
>     [CNum 9, -- increase quotient
>     -- if sub. underflow store rem in r8
>     CWhile 2 [
>       CNum (-2),
>       CWhile 1 [CNum (-1), CNum (-7)],
>       CWhile 7 [CNum (-7), CNum 8],
>       CNum (-9)
>     ]
>   ]),
>   CWhile 7 [CNum (-7)],         -- flush r7
>   CWhile 9 [CNum (-9), CNum 1], -- set quotient
>   CWhile 8 [CNum (-8), CNum 2]] -- set remainder

The idea is to keep subtracting until subtraction returns 1 in $r_2$ (second register), which means underflow. We keep track of the number of subtractions and then set $r_2 = r_2 - r_1$ for the remainder.

> egDiv1 = fastEvaluate [(1, 4), (2, 2)] arithDiv
> egDiv2 = fastEvaluate [(1, 4), (2, 3)] arithDiv

Exponents
---------

*Input*: $2^x \cdot 3^y$. *Output*: $2^n$.

This code sets $n$ to $x^y$.

> arithExp = [
>   CWhile 2 [CNum (-2), CNum 5], -- move r2 to r5
>   CWhile 1 [CNum (-1), CNum 6], -- set r6 to r1
>   CNum 1,                       -- start with 1
>   CWhile 5 ([CNum (-5),         -- while y>0
>     CWhile 6 [CNum (-6), CNum 7, CNum 2], -- set r7, r2 to r6
>     CWhile 7 [CNum (-7), CNum 6]]         -- bring r6 back
>     ++ arithMul),                         -- multiply
>   CWhile 6 [CNum (-6)]]         -- flush r6

> egExp = fastEvaluate [(1, 2), (2, 3)] arithExp

Logic gates
-----------

> logicNot = [CNum 2, CWhile 1 [CNum (-1), CNum (-2)], CWhile 2 [CNum (-2), CNum 1]]
> logicAnd = [CWhile 1 [CWhile 1 [CNum (-1)], CNum 3], CWhile 2 [CWhile 2 [CNum (-2)], CNum 3], CNum (-3), CWhile 3 [CNum (-3), CNum 1]]
> logicOr  = [CWhile 1 [CWhile 1 [CNum (-1)], CNum 3], CWhile 2 [CWhile 2 [CNum (-2)], CNum 3], CWhile 3 [CWhile 3 [CNum (-3)], CNum 1]]

> egNot  = [ (i, fastEvaluate [(1, i)] logicNot) | i <- [0..2]]
> egAnd  = [ (i, j, fastEvaluate [(1, i), (2, j)] logicAnd) | i <- [0..2], j <- [0..2]]
> egOr   = [ (i, j, fastEvaluate [(1, i), (2, j)] logicOr) | i <- [0..2], j <- [0..2]]

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
>   CNum 3,    -- r1 = input/output, r2 = 0, r3 = 1, r4 = 0, r5 = 0
>   CWhile 1     -- while n > 1
>     [CNum (-1),                     -- decrease n
>       CWhile 3 [CNum (-3), CNum 2, CNum 4], -- move r3 to r4, and add it to r2
>       CWhile 2 [CNum (-2), CNum 5],      -- move r2 to r5
>       CWhile 4 [CNum (-4), CNum 2],      -- move r4 to r2, and add it to r2
>       CWhile 5 [CNum (-5), CNum 3]],    -- move r5 to r3
>   CWhile 3 [CNum (-3)],      -- flush r3
>   CWhile 2 [CNum (-2), CNum 1]] -- move r2 to r1

> egFib = [ (i, fastEvaluate [(1, i)] fib) | i <- [0..6] ]

GCD
---

*Input*: $2^x \cdot 3^y$. *Output*: $2^n$.

Sets $n$ to $GCD(x, y)$.

> gcd' = [
>   CWhile 2
>     ([CWhile 2 [CNum (-2), CNum 11, CNum 12], -- copy b=r2 to r11, r12
>     CWhile 12 [CNum (-12), CNum 2]]       -- bring back b
>     ++ arithDiv ++
>     [CWhile 1 [CNum (-1)], CWhile 11 [CNum (-11), CNum 1]])] -- set a = b
>     -- b is already remainder

> egGcd1 = fastEvaluate [(1, 2), (2, 4)] gcd'
> egGcd2 = fastEvaluate [(1, 3), (2, 5)] gcd'
> egGcd3 = fastEvaluate [(1, 12), (2, 16)] gcd'

Primality test
--------------

*Input*: $2^x$. *Output*: $2^n$.

Sets $n$ to 1 if $x$ is prime, and 0 otherwise. Requires $x>1$.

> isPrime = [
>   CWhile 1 [CNum (-1), CNum 11, CNum 12],      -- copy r1 to r11/r12
>   CWhile 11
>     ([CWhile 12 [CNum (-12), CNum 1, CNum 15], -- first argument is original input
>     CWhile 15 [CNum (-15), CNum 12],           -- save original value from r15 (tmp) to r12
>     CWhile 2 [CNum (-2)],
>     CWhile 11 [CNum (-11), CNum 15],           -- copy r11 to r15
>     CWhile 15 [CNum (-15), CNum 2, CNum 11]]   -- second argument is current iterator
>     ++ arithDiv ++                             -- do the division
>     [
>     -- if there was a non-zero remainder, increase r14 (no factors)
>     CWhile 2 [CWhile 2 [CNum (-2)], CNum 14],
>     CNum (-11),
>     CWhile 1 [CNum (-1)]                       -- flush r1 (from division)
>   ]),
>   CWhile 12 [CNum (-12), CNum 1],     -- move r12 to r1 (total factors)
>   CWhile 14 [CNum (-14), CNum (-1)],  -- subtract r14 from r1 (total factors - no factors)
>   -- at this point, r1 contains the number of factors
>   -- if it's a prime, the number of factors will be two.
>   CNum (-1), CNum (-1),               -- if prime, r1 = 0, else r1 > 1
>   -- negate r1 for final result
>   CNum 2, CWhile 1 [CNum (-1), CNum (-2)], CWhile 2 [CNum (-2), CNum 1]]

The idea is to store in $r_{12}$ the result of `!(n%i)` for `i=n;i>=0`. We say that a number is prime if $r_{12}=2$, i.e. only two numbers divide the number (1 and itself).

> egPrime = [ (i, fastEvaluate [(1, i)] isPrime) | i <- [2..9] ]

Finding prime numbers
---------------------

*Input*: $2^x$. *Output*: $2^n$.

Sets $n$ to the first prime number greater/lower than $x$.

> findNextPrime = [
>   CWhile 1 [CNum (-1), CNum 17], -- store r1 to r17
>   CNum 1,                        -- set prime flag
>   CWhile 1 ([CNum (-1),          -- unset prime flag
>     CNum 17,                                 -- increase current number
>     CWhile 17 [CNum (-17), CNum 1, CNum 18], -- store r17 into r1 and r18
>     CWhile 18 [CNum (-18), CNum 17]]         -- bring back r17
>     ++ isPrime ++                            -- prime check
>     -- negate r1
>     [CNum 2, CWhile 1 [CNum (-1), CNum (-2)], CWhile 2 [CNum (-2), CNum 1]]),
>     CWhile 17 [CNum (-17), CNum 1]]          -- store result in r17

> egNextPrime = [ (i, fastEvaluate [(1, i)] findNextPrime) | i <- [2..9] ]

> findPrevPrime = [
>   CWhile 1 [CNum (-1), CNum 17], -- store r1 to r17
>   CNum 1,                        -- set prime flag
>   CWhile 1 ([CNum (-1),          -- unset prime flag
>     CNum (-17),                              -- increase current number
>     CWhile 17 [CNum (-17), CNum 1, CNum 18], -- store r17 into r1 and r18
>     CWhile 18 [CNum (-18), CNum 17]]         -- bring back r17
>     ++ isPrime ++                            -- prime check
>     -- negate r1
>     [CNum 2, CWhile 1 [CNum (-1), CNum (-2)], CWhile 2 [CNum (-2), CNum 1]]),
>     CWhile 17 [CNum (-17), CNum 1]]          -- store result in r17

> egPrevPrime = [ (i, fastEvaluate [(1, i)] findPrevPrime) | i <- [3..9] ]

Stack implementation (push)
---------------------------

*Input*: $2^x \cdot 67^y \cdot 71^z$. *Output*: $2^x \cdot 67^{y \cdot w^x} \cdot 71^w$, where $w$ is the first prime after $z$.

> stackPush = [
>   CWhile 1 [CNum (-1), CNum 21, CNum 22],
>   CWhile 20 [CNum (-20), CNum 1]]
>   ++ findNextPrime ++
>   [CWhile 1 [CNum (-1), CNum 20],
>   CWhile 21 [CNum (-21), CNum 2],
>   CWhile 20 [CNum (-20), CNum 1, CNum 21],
>   CWhile 21 [CNum (-21), CNum 20]]
>   ++ arithExp ++
>   [CWhile 19 [CNum (-19), CNum 2]]
>   ++ arithMul ++
>   [CWhile 1 [CNum (-1), CNum 19],
>   CWhile 22 [CNum (-22), CNum 1]]

The idea is to store the current prime number in $r_{20}$, and whenever an element is pushed, we find the next prime number and store it in $r_{20}$ and multiply $r_{19}$ by this prime times the value of the element being pushed. That is, the value of $r_{19}$ represents Gödel numbering, similar to how Budge-PL is implemented. If we push 3, 2, and 1 to the stack, note that the value of $r_{19}$ would be $2^3 \cdot 3^2 \cdot 5^1 = 360$.

> egStackEmpty = [(19, 1), (20, 1)]
> egStack1 = fastEvaluate (egStackEmpty ++ [(1, 3)]) stackPush
> egStack2 = fastEvaluate (egStack1 ++ [(1, 2)]) stackPush
> egStack3 = fastEvaluate (egStack2 ++ [(1, 1)]) stackPush

Stack implementation (pop)
--------------------------

*Input*: $67^{{p_1}^{k_1} \cdot {p_2}^{k_2} \cdot \ldots \cdot {p_n}^{k_n}} \cdot 71^{p_n}$. *Output*: $2^{k_n} \cdot 67^{{p_1}^{k_1} \cdot {p_2}^{k_2} \cdot \ldots \cdot {p_{n-1}}^{k_{n-1}}} \cdot 71^{p_{n-1}}$, where $p_n$ denotes the $n$-th prime number ($n$-th position), and $k_n$ denotes the value of the $n$-th position.

> stackPop = [
>   CNum 2, -- set remainder flag
>   CWhile 1 [CNum (-1)], CWhile 19 [CNum (-19), CNum 1],
>   CWhile 2 ([
>     CWhile 19 [CNum (-19)],
>     CWhile 1 [CNum (-1), CNum 19], -- flush number
>     CNum (-2), -- flush remainder
>     CWhile 19 [CNum (-19), CNum 1, CNum 21],
>     CWhile 21 [CNum (-21), CNum 19],
>     CWhile 20 [CNum (-20), CNum 2, CNum 21],
>     CWhile 21 [CNum (-21), CNum 20]]
>     ++ arithDiv ++
>     -- negate r2
>     [CNum 3, CWhile 2 [CNum (-2), CNum (-3)], CWhile 3 [CNum (-3), CNum 2],
>     CNum 22 -- increase count
>   ]),
>   CWhile 1 [CNum (-1)],
>   CWhile 20 [CNum (-20), CNum 1]]
>   ++ findPrevPrime ++
>   [CWhile 1 [CNum (-1), CNum 20],
>   CNum (-22), -- adjust value
>   CWhile 22 [CNum (-22), CNum 1]]

Similarly to the push implementation, the idea is to store the current prime number in $r_{20}$, and whenever an element is popped, we find the previous prime number and store it in $r_{20}$ and divide $r_{19}$ by the previous prime as long as division doesn't return a remainder.

> egStack4 = fastEvaluate egStack3 stackPop
> egStack5 = fastEvaluate egStack4 stackPop
> egStack6 = fastEvaluate egStack5 stackPop

Logarithm
---------

*Input*: $2^x \cdot 3^y$. *Output*: $2^n$.

Sets $n$ to $log_y(x)$.

> logn = [
>   CWhile 2 [CNum (-2), CNum 12], -- store r2 to r12
>   CWhile 1 -- while the first argument is non-zero
>     ([CWhile 2 [CNum (-2)],             -- flush r2
>     CWhile 15 [CNum (-15)],            -- flush r15
>     CWhile 12 [CNum (-12), CNum 2, CNum 15], -- restore r2 and save it to r3
>     CWhile 15 [CNum (-15), CNum 12]]      -- restore r12
>     ++ arithDiv ++                -- divide r1 by r2
>     -- negate r2 (see logical gate "Not")
>     [CWhile 3 [CNum (-3)], CNum 3, CWhile 2 [CNum (-2), CNum (-3)], CWhile 3 [CNum (-3), CNum 2],
>     CNum 11]),                       -- increase division count
>     CNum (-11), -- no off by one error
>     CWhile 11 [CNum (-11), CNum 1], -- flush r11 and move to r1
>     CWhile 12 [CNum (-12)]]      -- flush r12

> egLog2 = [ (i, fastEvaluate [(1, i), (2, 2)] logn) | i <- [2..8] ]
> egLog3 = [ (i, fastEvaluate [(1, i), (2, 3)] logn) | i <- [3..9] ]
