/-
The same generic set-coded small-category interface as `main.lit`, expressed
in pure Lean 4 with no imports.

Lean types represent the two set-sized carriers Obj and Mor. Hom is a family
of predicates on Mor, and subtypes represent precisely typed arrows. This is
handwritten comparison material, not generated Litex-to-Lean output.
-/

universe u v

namespace GenericSmallCategorySameMathInLean

abbrev Set (X : Type u) := X → Prop

abbrev HomArrow {Obj : Type u} {Mor : Type v}
    (Hom : Obj → Obj → Set Mor) (source target : Obj) :=
  {arrow : Mor // Hom source target arrow}

abbrev IdentityAssignment {Obj : Type u} {Mor : Type v}
    (Hom : Obj → Obj → Set Mor) :=
  (object : Obj) → HomArrow Hom object object

abbrev Composition {Obj : Type u} {Mor : Type v}
    (Hom : Obj → Obj → Set Mor) :=
  (source middle target : Obj) →
    HomArrow Hom source middle →
    HomArrow Hom middle target →
    HomArrow Hom source target

def IsMorphism {Obj : Type u} {Mor : Type v}
    (Hom : Obj → Obj → Set Mor) (source target : Obj) (f : Mor) : Prop :=
  Hom source target f

def IsIdentityMorphism {Obj : Type u} {Mor : Type v}
    (Hom : Obj → Obj → Set Mor) (compose : Composition Hom)
    (object : Obj) (identityArrow : HomArrow Hom object object) : Prop :=
  (∀ (target : Obj) (f : HomArrow Hom object target),
      compose object object target identityArrow f = f) ∧
  (∀ (source : Obj) (g : HomArrow Hom source object),
      compose source object object g identityArrow = g)

def IsComposite {Obj : Type u} {Mor : Type v}
    (Hom : Obj → Obj → Set Mor) (compose : Composition Hom)
    (source middle target : Obj)
    (f : HomArrow Hom source middle) (g : HomArrow Hom middle target)
    (h : HomArrow Hom source target) : Prop :=
  h = compose source middle target f g

def IsCategory {Obj : Type u} {Mor : Type v}
    (Hom : Obj → Obj → Set Mor)
    (identity : IdentityAssignment Hom) (compose : Composition Hom) : Prop :=
  (∀ object : Obj,
      IsIdentityMorphism Hom compose object (identity object)) ∧
  (∀ (source middle target farTarget : Obj)
      (f : HomArrow Hom source middle)
      (g : HomArrow Hom middle target)
      (h : HomArrow Hom target farTarget),
      compose source target farTarget
          (compose source middle target f g) h =
        compose source middle farTarget f
          (compose middle target farTarget g h))

theorem categoryIdentityIsIdentityMorphism
    {Obj : Type u} {Mor : Type v} (Hom : Obj → Obj → Set Mor)
    (identity : IdentityAssignment Hom) (compose : Composition Hom)
    (hCategory : IsCategory Hom identity compose) (object : Obj) :
    IsIdentityMorphism Hom compose object (identity object) :=
  hCategory.1 object

theorem categoryCompositionIsAMorphism
    {Obj : Type u} {Mor : Type v} (Hom : Obj → Obj → Set Mor)
    (compose : Composition Hom) (source middle target : Obj)
    (f : HomArrow Hom source middle) (g : HomArrow Hom middle target) :
    IsMorphism Hom source target (compose source middle target f g).1 :=
  (compose source middle target f g).2

theorem selectedCompositeIsComposite
    {Obj : Type u} {Mor : Type v} (Hom : Obj → Obj → Set Mor)
    (compose : Composition Hom) (source middle target : Obj)
    (f : HomArrow Hom source middle) (g : HomArrow Hom middle target) :
    IsComposite Hom compose source middle target f g
      (compose source middle target f g) := by
  rfl

namespace Terminal

-- There is one object and one arrow.
abbrev Obj := Unit
abbrev Mor := Unit

def Hom (_source _target : Obj) : Set Mor :=
  fun _arrow => True

def identity : IdentityAssignment Hom :=
  fun _object => ⟨(), True.intro⟩

def compose : Composition Hom :=
  fun _source _middle _target _f _g => ⟨(), True.intro⟩

theorem isCategory : IsCategory Hom identity compose := by
  constructor
  · intro object
    constructor
    · intro target f
      apply Subtype.ext
      cases f.1
      rfl
    · intro source g
      apply Subtype.ext
      cases g.1
      rfl
  · intro source middle target farTarget f g h
    rfl

end Terminal

namespace TwoObjectChaotic

-- The objects are false and true. The unique arrow source -> target is the
-- ordered pair (source, target).
abbrev Obj := Bool
abbrev Mor := Bool × Bool

def Hom (source target : Obj) : Set Mor :=
  fun arrow => arrow = (source, target)

def identity : IdentityAssignment Hom :=
  fun object => ⟨(object, object), rfl⟩

def compose : Composition Hom :=
  fun source _middle target _f _g =>
    ⟨(source, target), rfl⟩

theorem isCategory : IsCategory Hom identity compose := by
  constructor
  · intro object
    constructor
    · intro target f
      apply Subtype.ext
      exact f.property.symm
    · intro source g
      apply Subtype.ext
      exact g.property.symm
  · intro source middle target farTarget f g h
    rfl

end TwoObjectChaotic

end GenericSmallCategorySameMathInLean
