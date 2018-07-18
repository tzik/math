
module test where

mp : {A B C : Set} -> (A -> B) -> (B -> C) -> (A -> C)
mp f g x = g (f x)
