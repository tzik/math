open import Data.Product using (proj₁; proj₂)
open import Level using (_⊔_)
open import Algebra using (Group)
open import Algebra.Structures using (IsGroup)
open import Relation.Binary.Core using (_Preserves_⟶_)
import algebra.Subgroup

module algebra.Homomorphism {a b c d}
  (G : Group a b) (H : Group c d)
  (φ : Group.Carrier G → Group.Carrier H) where


Homomorphic : Set (a ⊔ d)
Homomorphic = ∀ x y → φ (x ∙' y) ≈ φ x ∙ φ y
  where open Group G using () renaming (_∙_ to _∙'_)
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
      φ (x * y) ≈⟨ hom x y ⟩ 
      φ x ∙ φ y ≈⟨ ∙-cong x∈kerφ y∈kerφ ⟩ 
      ε ∙ ε ≈⟨ proj₁ identity ε ⟩ 
      ε ∎
    where open Group G using () renaming (_∙_ to _*_)
          open Group H

  ε∈Kerφ : ε-Consistent
  ε∈Kerφ =
    begin⟨ Group.setoid H ⟩
      φ I ≈⟨ sym (proj₂ identity (φ I)) ⟩ 
      φ I ∙ ε ≈⟨ ∙-cong refl (sym (proj₂ inverse (φ I))) ⟩ 
      φ I ∙ (φ I ∙ φ I ⁻¹) ≈⟨ sym (assoc (φ I) (φ I) (φ I ⁻¹)) ⟩ 
      φ I ∙ φ I ∙ φ I ⁻¹ ≈⟨ ∙-cong (sym (hom I I)) refl ⟩ 
      φ (I * I) ∙ φ I ⁻¹ ≈⟨ ∙-cong (φ-cong (proj₁ G-identity I)) refl ⟩ 
      φ I ∙ φ I ⁻¹ ≈⟨ proj₂ inverse (φ I) ⟩ 
      ε ∎
    where open Group G using () renaming (ε to I; _⁻¹ to inv; _∙_ to _*_)
          open Group H using (_∙_; ε; _⁻¹)
          open IsGroup (Group.isGroup G) using () renaming (identity to G-identity)
          open IsGroup (Group.isGroup H)
  
  x∈Kerφ⇒x⁻¹∈Kerφ : ⁻¹-Consistent
  x∈Kerφ⇒x⁻¹∈Kerφ  {x} x∈kerφ = 
    begin⟨ Group.setoid H ⟩
      φ (inv x) ≈⟨ sym (proj₁ identity (φ (inv x))) ⟩
      ε ∙ φ (inv x) ≈⟨ ∙-cong (sym x∈kerφ) refl ⟩
      φ x ∙ φ (inv x) ≈⟨ sym (hom x (inv x)) ⟩
      φ (x * inv x) ≈⟨ φ-cong (proj₂ G-inverse x) ⟩
      φ I ≈⟨ ε∈Kerφ ⟩
      ε ∎
    where open Group G using () renaming (_∙_ to _*_; _⁻¹ to inv; ε to I)
          open Group H using (_∙_; ε; _⁻¹)
          open IsGroup (Group.isGroup H)
          open IsGroup (Group.isGroup G) using () renaming (inverse to G-inverse)

  Kernel : Group (a ⊔ d) b
  Kernel = Subgroup Kerφ∙Kerφ⊂Kerφ x∈Kerφ⇒x⁻¹∈Kerφ ε∈Kerφ
