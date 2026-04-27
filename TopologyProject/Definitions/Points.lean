import TopologyProject.Definitions.Continuity

/- Neighborhood-space layer used by the point functor constructions. -/

structure NbhdSpace where
  Point : Type

def NbhdHom (A B : NbhdSpace) := A.Point → B.Point

def PtObj {X : Type} (_S : FormalTopology X) : NbhdSpace :=
  { Point := Subset X }

def PtMap {X Y : Type}
    (_S : FormalTopology X) (_T : FormalTopology Y)
    (R : X → Y → Prop) : NbhdHom (PtObj _S) (PtObj _T) :=
  λ α => λ y => ∃ x, α x ∧ R x y

def pointBasicStar {X : Type} (a : X) : Subset (Subset X) :=
  λ α => α a

postfix:max "⋆" => pointBasicStar

def imageSubset {A B : Type} (f : A → B) (U : Subset A) : Subset B :=
  λ b => ∃ a, U a ∧ f a = b

def subsetIncl {X : Type} (U V : Subset X) : Prop :=
  ∀ x, U x → V x

notation U " ⊆ₛ " V => subsetIncl U V

/- Minimal packaging for object and map data on the Nbhd side. -/

structure SimpleFunctor where
  obj : NbhdSpace
  map : obj.Point → obj.Point
def nbhdComp (A B C : NbhdSpace) (f : NbhdHom A B) (g : NbhdHom B C) : NbhdHom A C :=
  λ x => g (f x)

def PtMapC {X Y : Type}
    {S : FormalTopology X} {T : FormalTopology Y}
    (f : ContinuousMapping S T) : NbhdHom (PtObj S) (PtObj T) :=
  PtMap S T f.rel

def uniformlyContinuousPtMap
    {X Y : Type}
    (S : FormalTopology X) (T : FormalTopology Y)
    (g : NbhdHom (PtObj S) (PtObj T)) : Prop :=
  ∀ b : Y, ∃ a : X, imageSubset g (a⋆) ⊆ₛ (b⋆)

structure PackagedPt where
  S : NbhdSpace
  T : NbhdSpace
  map : NbhdHom S T

def PtPack {X Y : Type}
    (S : FormalTopology X) (T : FormalTopology Y)
    (f : ContinuousMapping S T) : PackagedPt :=
  { S := PtObj S
    T := PtObj T
    map := PtMapC f }

def natOrderComposedContinuous : ContinuousMapping natFormalTopology natFormalTopology :=
  natOrderContinuous ⊚c natOrderContinuous
