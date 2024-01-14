------------------------------------------------------------------------
-- Coursework 0: Install
------------------------------------------------------------------------

-- 1. Install Agda version 2.6.4.1
--    cf. https://agda.readthedocs.io/en/v2.6.4.1/getting-started/installation.html

-- 2. Install and configure an editor
--    cf. https://agda.readthedocs.io/en/v2.6.4.1/tools/emacs-mode.html

-- 3. Install the Standard Library version 2.0
--    cf. https://github.com/agda/agda-stdlib/blob/master/doc/installation-guide.md
--    Don't forget the last step to make the library a default one

-- If you have successfully followed these steps, the following file should
-- load without any issue. By pressing `C-c C-l` the module should be semantically
-- highlighted.

-- Running `make` in the courseworks directory should successfully compile the
-- file and you should then be able to run your first Agda program by executing
-- `./00-Install`.

{-# OPTIONS --erasure --guardedness #-}

module 00-Install where

open import Data.String.Base
open import IO.Base
open import IO.Finite
open import IO.Effectful
open import IO.Instances

main : Main
main = run do
  putStrLn "What is your name?"
  str ← getLine
  putStrLn ("Hello " ++ str ++ "!")
