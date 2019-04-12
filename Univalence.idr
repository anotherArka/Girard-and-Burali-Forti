module Univalence

%access public export
%default total

Homotopy : (ty1 ,ty2 : Type) -> (f, g : ty1 -> ty2) -> Type
Homotopy ty1 ty2 f g = (x : ty1) -> ( (f x) = (g x) )

IsQInv : (ty1 ,ty2 : Type) -> (f : ty1 -> ty2) -> (g : ty2 -> ty1) -> Type
IsQInv ty1 ty2 f g = (Homotopy ty1 ty1 (g . f) id, Homotopy ty2 ty2 (f . g) id)

QInv : (ty1 ,ty2 : Type) -> (f : ty1 -> ty2) -> Type
QInv ty1 ty2 f = (g : (ty2 -> ty1) ** (IsQInv ty1 ty2 f g))

IsEquiv : (ty1, ty2 : Type) -> (f : ty1 -> ty2) -> Type
IsEquiv ty1 ty2 f = 
    (( g : (ty2 -> ty1) ** ((Homotopy ty1 ty1 (g . f) id))),
     ( g : (ty2 -> ty1) ** ((Homotopy ty1 ty1 (g . f) id))))
     
Equiv : (ty1, ty2 : Type) -> Type
Equiv ty1 ty2 = (f : (ty1 -> ty2) ** (IsEquiv ty1 ty2 f))     
     
IdToEquiv : (ty1, ty2 : Type) -> (ty1 = ty2) -> (Equiv ty1 ty2)
IdToEquiv ty ty Refl = (id ** ((id ** trivial_homotopy) , 
                              (id ** trivial_homotopy))) where
    trivial_homotopy : (x : ty) -> (x = x)
    trivial_homotopy x = Refl
    
EquivToId : (ty1, ty2 : Type) -> (Equiv ty1 ty2) -> (ty1 = ty2)
--EquivToId ty ty _ = Refl
EquivToId ty1 ty2 pfE = assert_total (EquivToId ty1 ty2 pfE)

