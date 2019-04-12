module Prop

%access public export
%default total

IsProp : (t : Type) -> Type
IsProp t = (a, b : t) -> (a = b)









