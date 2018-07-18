
open import Function using (_on_; _∘_)
open import Data.Product using (Σ; proj₁; proj₂; _,_)
open import Level using (Level; _⊔_)
open import Relation.Binary using (IsEquivalence; Setoid)
open import Algebra using (Group)
open import Algebra.Structures using (IsGroup)

module algebra.Subgroup {a c l}
  (G : Group c l) (p : Group.Carrier G → Set a) where

open Group G hiding (isGroup)
open IsGroup (Group.isGroup G) renaming (
  ⁻¹-cong to G-⁻¹-cong;
  inverse to G-inverse;
  identity to G-identity;
  assoc to G-assoc;
  ∙-cong to G-∙-cong;
  refl to G-refl;
  sym to G-sym;
  trans to G-trans)

∙-Consistent : Set (a ⊔ c)
∙-Consistent = ∀ {x y} → p x → p y → p (x ∙ y)

⁻¹-Consistent :  Set (a ⊔ c)
⁻¹-Consistent  = ∀ {x} → p x → p (x ⁻¹)

-- Note: ∙-Consistent and ⁻¹-Consistent imply ε-Consistent, unless Carrier is empty.
ε-Consistent : Set a
ε-Consistent = p ε

Subgroup : ∙-Consistent → ⁻¹-Consistent  → ε-Consistent  → Group (a ⊔ c) l
Subgroup prod inv id = record {
    Carrier = Σ Carrier p;
    _≈_ = _≈_ on proj₁;
    _∙_ = λ x y → (_∙_ on proj₁) x y , prod (proj₂ x) (proj₂ y);
    ε = ε , id;
    _⁻¹ = λ x → (proj₁ x) ⁻¹ , inv (proj₂ x);
    isGroup = record {
      ⁻¹-cong = G-⁻¹-cong;
      inverse = proj₁ inverse ∘ proj₁ , proj₂ inverse ∘ proj₁;
      isMonoid = record {
        identity = proj₁ G-identity ∘ proj₁ , proj₂ G-identity ∘ proj₁;
        isSemigroup = record {
          assoc = λ x y z → G-assoc (proj₁ x) (proj₁ y) (proj₁ z) ;
          ∙-cong = λ x≈y z≈w → G-∙-cong x≈y z≈w;
          isEquivalence = record {
            refl = G-refl; sym = G-sym; trans = G-trans
          } 
        }
      }
    }
  }
