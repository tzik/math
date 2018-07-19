
open import Algebra.FunctionProperties using (LeftInverse; RightInverse; LeftIdentity; RightIdentity; Congruent₁; Congruent₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Algebra using (Group)
open import Relation.Binary using (Rel; IsEquivalence; _⇒_)
open import Algebra.Structures using (IsGroup)

module algebra.Quotient {a b c}
  (G : Group a b)
  (_∼_ :  Rel (Group.Carrier G) c)
  (isEquivalence : IsEquivalence _∼_) where

open Group G using (Carrier; _∙_; ε; _⁻¹; _≈_)
open IsGroup (Group.isGroup G) using (inverse; identity; assoc)

QuotientGroup : _≈_ ⇒ _∼_ → Congruent₂ _∼_ _∙_ → Congruent₁ _∼_ _⁻¹ → Group a c
QuotientGroup ≈⇒∼  ∙-cong ⁻¹-cong = record {
    Carrier = Carrier;
    _≈_ = _∼_;
    _∙_ = _∙_;
    ε = ε;
    _⁻¹ = _⁻¹;
    isGroup = record {
      inverse = left-inverse , right-inverse;
      ⁻¹-cong = ⁻¹-cong;
      isMonoid = record {
        identity = left-identity , right-identity;
        isSemigroup = record {
          assoc = λ x y z → ≈⇒∼ (assoc x y z);
          ∙-cong = ∙-cong;
          isEquivalence = isEquivalence
        }
      }
    }
  }
  where left-inverse : LeftInverse _∼_ ε _⁻¹ _∙_
        left-inverse x = ≈⇒∼ (proj₁ inverse x)
        right-inverse : RightInverse _∼_ ε _⁻¹ _∙_
        right-inverse x = ≈⇒∼ (proj₂ inverse x)
        left-identity : LeftIdentity _∼_ ε _∙_
        left-identity x = ≈⇒∼ (proj₁ identity x)
        right-identity : RightIdentity _∼_ ε _∙_
        right-identity x = ≈⇒∼ (proj₂ identity x)
