module Girard

-- a try to prove Girard's paradox in Idris

%access public export
%default total

data copy_of : (ty : Type) -> Type where
    paste : ty -> (copy_of ty)

||| The smallest ordinal
data Ord_0 : Type where

data Next_Ord : (ordinal : Type) -> Type where
    itself : Next_Ord ordinal
    inc : ordinal -> (Next_Ord ordinal)

data Induced_Order : (ordinal : Type) -> (order : ordinal -> ordinal -> Type) ->
                     (Next_Ord ordinal) -> (Next_Ord ordinal) -> Type where
    topping : (a : ordinal) -> (Induced_Order ordinal order (inc a) ifself)
    induce : (a, b : ordinal) -> (order a b) -> (Induced_Order ordinal order (inc a) (inc b))

Is_Irreflexive : (typ : Type) -> (p : (typ -> typ -> Type)) -> Type
Is_Irreflexive typ p = (a : typ) -> (p a a) -> Void

Property_0 : (p : Void -> Void -> Type) -> (Is_Irreflexive Void p)
Property_0 p a pf = a

Property_1 : (ordinal : Type) -> (order : (ordinal -> ordinal -> Type)) ->
             (Is_Irreflexive ordinal order) -> (a : (Next_Ord ordinal)) ->
             (Induced_Order ordinal order itself a)  -> Void

Property_1 ordinal order pfIrr itself (topping a) = ?rhs_2
Property_1 ordinal order pfIrr (inc b) (induce a b x) = ?rhs_3
Property_1 ordinal order pfIrr (inc x) (topping a) = ?rhs_1
Property_1 ordinal order pfIrr (inc x) (induce a x y) = ?rhs_5

{-
Property_2 : (ordinal : Type) -> (order : (ordinal -> ordinal -> Type)) ->
             (Is_Irreflexive ordinal order) ->
             (Is_Irreflexive (Next_Ord ordinal order) (Induced_Order ordinal order))

Property_2 ordinal order pfIrr (inc a) (induce a a pf) = pfIrr a pf
-}
