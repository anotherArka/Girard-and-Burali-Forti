module Girard

-- a try to prove Girard's paradox in Idris

%access public export
%default total

data copy_of : (ty : Type) -> Type where
    paste : ty -> (copy_of ty) 

||| The smallest ordinal
data Ord_0 : Type where

data Next_Ord : (ordinal : Type) -> (order : ordinal -> ordinal -> Type) -> Type where
    itself : Next_Ord ordinal order
    inc : ordinal -> (Next_Ord ordinal order)

data Induced_Order : (ordinal : Type) -> (order : ordinal -> ordinal -> Type) -> 
                     (Next_Ord ordinal order) -> (Next_Ord ordinal order) -> Type where
    topping : (a : ordinal) -> (Induced_Order ordinal order (inc a) ifself) 
    induce : (a, b : ordinal) -> (order a b) -> (Induced_Order ordinal order (inc a) (inc b))
    
    
    

