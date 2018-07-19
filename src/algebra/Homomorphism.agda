open import Function using (_$_)
open import Data.Product using (proj₁; proj₂; ∃; _,_)
open import Level using (_⊔_)
open import Algebra using (Group)
open import Algebra.Structures using (IsGroup)
open import Relation.Binary.Core using (_Preserves_⟶_)
import algebra.Subgroup

module algebra.Homomorphism {a b c d}
  (G : Group a b) (H : Group c d)
  (φ : Group.Carrier G → Group.Carrier H) where

module Group-Lemma {a' b'} (G : Group a'  b') where
  open Group G using (Carrier; _≈_; _∙_; _⁻¹; ε)
  open IsGroup (Group.isGroup G)
  open import Relation.Binary.SetoidReasoning using (begin⟨_⟩_; _∎; _≈⟨_⟩_)

  cancelˡ : {x y : Carrier} → (z : Carrier) → z ∙ x ≈ z ∙ y → x ≈ y
  cancelˡ {x} {y} z z∙x≈z∙y =
    begin⟨ Group.setoid G ⟩
      x ≈⟨ sym (proj₁ identity x) ⟩
      ε ∙ x ≈⟨ ∙-cong (sym (proj₁ inverse z)) refl ⟩
      z ⁻¹ ∙ z ∙ x ≈⟨ assoc (z ⁻¹) z x ⟩
      z ⁻¹ ∙ (z ∙ x) ≈⟨ ∙-cong refl z∙x≈z∙y ⟩
      z ⁻¹ ∙ (z ∙ y) ≈⟨ sym (assoc (z ⁻¹) z y) ⟩
      z ⁻¹ ∙ z ∙ y ≈⟨ ∙-cong (proj₁ inverse z) refl ⟩
      ε ∙ y ≈⟨ proj₁ identity y ⟩
      y ∎

  cancelʳ : {x y : Carrier} → (z : Carrier) → x ∙ z ≈ y ∙ z → x ≈ y
  cancelʳ {x} {y} z x∙z≈y∙z =
    begin⟨ Group.setoid G ⟩
      x ≈⟨ sym (proj₂ identity x) ⟩
      x ∙ ε ≈⟨ ∙-cong refl (sym (proj₂ inverse z)) ⟩
      x ∙ (z ∙ z ⁻¹)  ≈⟨ sym (assoc x z (z ⁻¹)) ⟩
      x ∙ z ∙ z ⁻¹  ≈⟨ ∙-cong x∙z≈y∙z refl ⟩
      y ∙ z ∙ z ⁻¹  ≈⟨ assoc y z (z ⁻¹) ⟩
      y ∙ (z ∙ z ⁻¹)  ≈⟨ ∙-cong refl (proj₂ inverse z) ⟩
      y ∙ ε ≈⟨ proj₂ identity y ⟩
      y ∎

Homomorphic : Set (a ⊔ d)
Homomorphic = ∀ x y → φ (x + y) ≈ φ x ∙ φ y
  where open Group G using () renaming (_∙_ to _+_)
        open Group H using (_∙_; _≈_)

record Homomorphism : Set (a ⊔ b ⊔ d) where
  field
    hom : Homomorphic
    φ-cong : φ Preserves Group._≈_  G ⟶ Group._≈_ H

module Ker (A : Homomorphism) where
  open Homomorphism A

  x∈Kerφ : Group.Carrier G → Set d
  x∈Kerφ x = φ x ≈ ε
    where open Group H

  open algebra.Subgroup G x∈Kerφ
  open import Relation.Binary.SetoidReasoning

  Kerφ∙Kerφ⊂Kerφ : ∙-Consistent
  Kerφ∙Kerφ⊂Kerφ {x} {y} x∈kerφ y∈kerφ =
    begin⟨ Group.setoid H ⟩
      φ (x + y) ≈⟨ hom x y ⟩
      φ x ∙ φ y ≈⟨ ∙-cong x∈kerφ y∈kerφ ⟩
      ε ∙ ε ≈⟨ proj₁ identity ε ⟩
      ε ∎
    where open Group G using () renaming (_∙_ to _+_)
          open Group H

  ε∈Kerφ : ε-Consistent
  ε∈Kerφ = cancelˡ (φ 0#) $
    begin⟨ Group.setoid H ⟩
      φ 0# ∙ φ 0# ≈⟨ sym (hom 0# 0#) ⟩
      φ (0# + 0#) ≈⟨ φ-cong (proj₂ G-identity 0#) ⟩
      φ 0#  ≈⟨ sym (proj₂ identity (φ 0#)) ⟩
      φ 0# ∙ ε ∎
    where open Group-Lemma H using (cancelˡ)
          open Group G using  () renaming (ε to 0#; _∙_ to _+_; identity to G-identity)
          open Group H

  x∈Kerφ⇒x⁻¹∈Kerφ : ⁻¹-Consistent
  x∈Kerφ⇒x⁻¹∈Kerφ  {x} x∈kerφ = cancelˡ (φ x) $
    begin⟨ Group.setoid H ⟩
      φ x ∙ φ (- x) ≈⟨ sym (hom x (- x)) ⟩
      φ (x + (- x)) ≈⟨ φ-cong (proj₂ G-inverse x) ⟩
      φ 0# ≈⟨ ε∈Kerφ ⟩
      ε ≈⟨ sym x∈kerφ ⟩
      φ x ≈⟨ sym (proj₂ identity (φ x)) ⟩
      φ x ∙ ε ∎
    where open Group-Lemma H using (cancelˡ)
          open Group H
          open Group G using () renaming (_⁻¹ to -_; _∙_ to _+_; ε to 0#; inverse to G-inverse)

  Kernel : Group (a ⊔ d) b
  Kernel = Subgroup Kerφ∙Kerφ⊂Kerφ x∈Kerφ⇒x⁻¹∈Kerφ ε∈Kerφ

module Im (A : Homomorphism) where
  open Homomorphism A

  y∈Imφ : Group.Carrier H → Set (a ⊔ d)
  y∈Imφ y = ∃ (λ x → φ x ≈ y)
    where open Group H

  open algebra.Subgroup H y∈Imφ
  open import Relation.Binary.SetoidReasoning

  Imφ∙Imφ⊂Imφ : ∙-Consistent
  Imφ∙Imφ⊂Imφ {s} {t} s∈imφ t∈imφ = x + y , p
    where open Group G using () renaming (_∙_ to _+_)
          open Group H
          x = proj₁ s∈imφ
          y = proj₁ t∈imφ
          φx≈s = proj₂ s∈imφ
          φy≈t = proj₂ t∈imφ
          p = begin⟨ Group.setoid H ⟩
                φ (x + y) ≈⟨ hom x y ⟩
                φ x ∙ φ y ≈⟨ ∙-cong φx≈s φy≈t ⟩
                s ∙ t ∎

  s∈Imφ⇒s⁻¹∈Imφ : ⁻¹-Consistent
  s∈Imφ⇒s⁻¹∈Imφ {s} s∈imφ = - x , cancelˡ s p
    where open Group-Lemma H using (cancelˡ)
          open Group G using () renaming (_⁻¹ to -_; _∙_ to _+_; ε to 0#)
          open Group H
          open IsGroup (Group.isGroup G) using () renaming (inverse to G-inverse)
          open Ker A using (ε∈Kerφ)
          x = proj₁ s∈imφ
          φx≈s = proj₂ s∈imφ
          p = begin⟨ Group.setoid H ⟩
            s ∙ φ (- x) ≈⟨ ∙-cong (sym φx≈s) refl ⟩
            φ x ∙ φ (- x) ≈⟨ sym (hom x (- x)) ⟩
            φ (x + (- x)) ≈⟨ φ-cong (proj₂ G-inverse x) ⟩
            φ 0# ≈⟨ ε∈Kerφ ⟩
            ε ≈⟨ sym (proj₂ inverse s) ⟩
            s ∙ s ⁻¹ ∎

  ε∈Imφ : ε-Consistent
  ε∈Imφ = 0# , ε∈Kerφ
    where open Group G using () renaming (ε to 0#)
          open Ker A using (ε∈Kerφ)

  Image : Group (a ⊔ c ⊔ d) d
  Image = Subgroup Imφ∙Imφ⊂Imφ s∈Imφ⇒s⁻¹∈Imφ  ε∈Imφ
