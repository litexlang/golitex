/-
Pure Lean 4 analogy for `main.lit`.

No imports are used. This is handwritten comparison code, not generated
Litex-to-Lean compiler output.
-/

universe u v w

namespace TopologyCoreAnalogy

abbrev Set (X : Type u) := X → Prop

def empty : Set X := fun _ => False
def full : Set X := fun _ => True
def intersect (A B : Set X) : Set X := fun x => A x ∧ B x
def union (A B : Set X) : Set X := fun x => A x ∨ B x
def complement (A : Set X) : Set X := fun x => ¬ A x
def preimage (f : X → Y) (V : Set Y) : Set X := fun x => V (f x)
def image (f : X → Y) (K : Set X) : Set Y :=
  fun y => ∃ x, K x ∧ f x = y
def bigUnion (family : Set (Set X)) : Set X :=
  fun x => ∃ member, family member ∧ member x

structure TopologicalSpaceSetting (X : Type u) where
  isOpen : Set (Set X)
  empty_mem : isOpen empty
  full_mem : isOpen full
  intersect_mem : ∀ {U V}, isOpen U → isOpen V → isOpen (intersect U V)
  bigUnion_mem : ∀ {family}, (∀ U, family U → isOpen U) → isOpen (bigUnion family)

theorem triple_intersection {X : Type u} (T : TopologicalSpaceSetting X)
    {A B C : Set X} (hA : T.isOpen A) (hB : T.isOpen B) (hC : T.isOpen C) :
    T.isOpen (intersect (intersect A B) C) :=
  T.intersect_mem (T.intersect_mem hA hB) hC

theorem binary_union {X : Type u} (T : TopologicalSpaceSetting X)
    {A B : Set X} (hA : T.isOpen A) (hB : T.isOpen B) :
    T.isOpen (union A B) := by
  let family : Set (Set X) := fun candidate => candidate = A ∨ candidate = B
  have family_is_open : ∀ U, family U → T.isOpen U := by
    intro U hU
    cases hU with
    | inl h => exact h ▸ hA
    | inr h => exact h ▸ hB
  have union_is_open : T.isOpen (bigUnion family) := T.bigUnion_mem family_is_open
  have same_set : bigUnion family = union A B := by
    funext x
    apply propext
    constructor
    · intro hx
      cases hx with
      | intro U h =>
          cases h with
          | intro hFamily hxU =>
              cases hFamily with
              | inl h => exact Or.inl (h ▸ hxU)
              | inr h => exact Or.inr (h ▸ hxU)
    · intro hx
      cases hx with
      | inl hxA => exact ⟨A, Or.inl rfl, hxA⟩
      | inr hxB => exact ⟨B, Or.inr rfl, hxB⟩
  exact same_set ▸ union_is_open

structure Continuous {X : Type u} {Y : Type v}
    (TX : TopologicalSpaceSetting X) (TY : TopologicalSpaceSetting Y)
    (f : X → Y) : Prop where
  preimage_open : ∀ {V}, TY.isOpen V → TX.isOpen (preimage f V)

theorem continuous_composition {A : Type u} {B : Type v} {C : Type w}
    {TA : TopologicalSpaceSetting A} {TB : TopologicalSpaceSetting B}
    {TC : TopologicalSpaceSetting C} {f : A → B} {g : B → C}
    (hf : Continuous TA TB f) (hg : Continuous TB TC g) :
    Continuous TA TC (fun x => g (f x)) where
  preimage_open := by
    intro targetOpen targetOpen_mem
    have middle_preimage_open : TB.isOpen (preimage g targetOpen) :=
      hg.preimage_open targetOpen_mem
    have nested_preimage_open : TA.isOpen (preimage f (preimage g targetOpen)) :=
      hf.preimage_open middle_preimage_open
    exact nested_preimage_open

def IsClosed {X : Type u} (T : TopologicalSpaceSetting X) (F : Set X) : Prop :=
  T.isOpen (complement F)

def HasClosedPreimages {X : Type u} {Y : Type v}
    (TX : TopologicalSpaceSetting X) (TY : TopologicalSpaceSetting Y)
    (f : X → Y) : Prop :=
  ∀ F, IsClosed TY F → IsClosed TX (preimage f F)

theorem preimage_of_complement {X : Type u} {Y : Type v}
    (f : X → Y) (F : Set Y) :
    preimage f (complement F) = complement (preimage f F) := rfl

theorem continuous_map_has_closed_preimages
    {X : Type u} {Y : Type v}
    {TX : TopologicalSpaceSetting X} {TY : TopologicalSpaceSetting Y}
    {f : X → Y} (continuous : Continuous TX TY f) :
    HasClosedPreimages TX TY f := by
  intro F closedF
  change TX.isOpen (complement (preimage f F))
  change TY.isOpen (complement F) at closedF
  exact continuous.preimage_open closedF

theorem closed_preimages_imply_continuous
    {X : Type u} {Y : Type v}
    {TX : TopologicalSpaceSetting X} {TY : TopologicalSpaceSetting Y}
    {f : X → Y} (closedPreimages : HasClosedPreimages TX TY f) :
    Continuous TX TY f where
  preimage_open := by
    intro U openU
    have complement_closed : IsClosed TY (complement U) := by
      change TY.isOpen (complement (complement U))
      have double_complement : complement (complement U) = U := by
        funext y
        apply propext
        constructor
        · intro hnnot
          exact Classical.byContradiction (fun hU => hnnot hU)
        · intro hU hnU
          exact hnU hU
      exact double_complement.symm ▸ openU
    have pullback_closed : IsClosed TX (preimage f (complement U)) :=
      closedPreimages (complement U) complement_closed
    change TX.isOpen (complement (preimage f (complement U))) at pullback_closed
    have target_eq : complement (preimage f (complement U)) = preimage f U := by
      funext x
      apply propext
      constructor
      · intro hnnot
        exact Classical.byContradiction (fun hU => hnnot hU)
      · intro hU hnU
        exact hnU hU
    exact target_eq ▸ pullback_closed

inductive IsFiniteSet {Index : Type u} : Set Index → Prop where
  | empty : IsFiniteSet empty
  | insert (index : Index) {rest : Set Index} :
      IsFiniteSet rest → IsFiniteSet (fun candidate => candidate = index ∨ rest candidate)

def Covers {X : Type u} {Index : Type v}
    (K : Set X) (cover : Index → Set X) (indices : Set Index) : Prop :=
  ∀ x, K x → ∃ index, indices index ∧ cover index x

def IsCompactSubset {X : Type u}
    (T : TopologicalSpaceSetting X) (K : Set X) : Prop :=
  ∀ (Index : Type u) (cover : Index → Set X),
    (∀ index, T.isOpen (cover index)) →
    Covers K cover full →
    ∃ finiteIndices, IsFiniteSet finiteIndices ∧ Covers K cover finiteIndices

theorem continuous_image_of_compact_is_compact
    {X : Type u} {Y : Type u}
    {TX : TopologicalSpaceSetting X} {TY : TopologicalSpaceSetting Y}
    {f : X → Y} (continuous : Continuous TX TY f)
    {K : Set X} (compactK : IsCompactSubset TX K) :
    IsCompactSubset TY (image f K) := by
  intro Index cover coverOpen imageCovered
  let pullbackCover : Index → Set X := fun index => preimage f (cover index)
  have pullbackOpen : ∀ index, TX.isOpen (pullbackCover index) := by
    intro index
    exact continuous.preimage_open (coverOpen index)
  have sourceCovered : Covers K pullbackCover full := by
    intro x hx
    have imagePoint : image f K (f x) := ⟨x, hx, rfl⟩
    cases imageCovered (f x) imagePoint with
    | intro index h => exact ⟨index, True.intro, h.right⟩
  cases compactK Index pullbackCover pullbackOpen sourceCovered with
  | intro finiteIndices hfinite =>
      refine ⟨finiteIndices, hfinite.left, ?_⟩
      intro y hy
      cases hy with
      | intro x hx =>
          cases hx with
          | intro hxK hxy =>
              cases hfinite.right x hxK with
              | intro index hindex =>
                  refine ⟨index, hindex.left, ?_⟩
                  exact hxy ▸ hindex.right

end TopologyCoreAnalogy
