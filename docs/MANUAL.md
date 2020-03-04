# Writing a Program in GARUDA

These are somewhat outdated and very fuzzy right now, but this is the gist:



## Compile the src
(See install.md)

## In combinators.v
1. Write the program
2. Evaluate to the end using Proof General in Emacs
3. Run the output file
  - `runhaskell <src>.hs > <src>.v`

The more verbose way:
- use ghci to run the output Haskell file
  - `:l <src>.hs`
  - `Prelude.putStr pretty_print_<src>` (or putStrLn?)