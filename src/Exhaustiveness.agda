module Exhaustiveness where

open import Data.Bool using (true; false; _∧_)
open import Data.Fin as Fin using (zero; suc)
open import Data.Fin.Subset using (Subset; _∈_; _∉_; ⊥; ⁅_⁆; _∪_; ∁; ⋃; Nonempty; Empty)
open import Data.Fin.Subset.Properties using (x∈∁p⇒x∉p; x∉p⇒x∈∁p; ∉⊥; x∈⁅x⁆; x∈⁅y⁆⇔x≡y; nonempty?)
open import Data.Fin.Properties using (any?)
open import Data.List as List using (List; []; _∷_; _++_; concatMap)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties as Any using (¬Any[])
open import Data.List.Relation.Unary.First as First using (First; toAny)
open import Data.List.Relation.Unary.First.Properties as First using (All⇒¬First)
open import Data.Nat using (ℕ; zero; suc; _+_; _<′_; <′-base; <′-step)
open import Data.Nat.Induction using (<′-wellFounded)
open import Data.Nat.Properties using (+-comm; +-assoc; ≤⇒≤′; s≤′s; m≤n+m)
open import Data.Product as Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Function using (id; _∘_; _⇔_; mk⇔; Equivalence)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; ≢-sym)
open import Relation.Nullary.Decidable as Dec using (Dec; yes; no; _⊎-dec_; _×-dec_)
open import Relation.Nullary.Negation using (¬_; contradiction; contraposition)

open import Extra
open import Pattern

private
  variable
    α β : Ty
    αs βs : List Ty

--------------------------------------------------------------------------------
-- Exhaustiveness and usefulness

-- There is a matching row in P for every list of values
Exhaustive : PatMat αs → Set
Exhaustive P = ∀ vs → Match P vs

-- There is a list of values that does not match any row in P
NonExhaustive : PatMat αs → Set
NonExhaustive P = ∃[ vs ] ¬ Match P vs

-- ps is useful with respect to P if
--   1. there is a list of values that matches ps (say vs)
--   2. vs does not match any row in P
-- Usefulness can also be used to formulate redundancy
Useful : PatMat αs → Pats αs → Set
Useful P ps = ∃[ vs ] P ⋠** vs × ps ≼* vs

-- non-exhaustiveness defined in terms of usefulness:
-- P is non-exhaustive if ∙* is useful with respect to P
NonExhaustive′ : PatMat αs → Set
NonExhaustive′ P = Useful P ∙*

-- P is exhaustive if ∙* is not useful with respect to P
Exhaustive′ : PatMat αs → Set
Exhaustive′ P = ¬ NonExhaustive′ P

module _ {P : PatMat αs} where

  NonExhaustive′→NonExhaustive : NonExhaustive′ P → NonExhaustive P
  NonExhaustive′→NonExhaustive (vs , ∙*ps⋠vs , _) = vs , contraposition toAny ∙*ps⋠vs

  NonExhaustive→NonExhaustive′ : NonExhaustive P → NonExhaustive′ P
  NonExhaustive→NonExhaustive′ (vs , P⋠vs) = vs , ¬First⇒¬Any id P⋠vs , ∙*≼

  -- The two definitions of non-exhaustiveness are equivalent
  NonExhaustive′⇔NonExhaustive : NonExhaustive′ P ⇔ NonExhaustive P
  NonExhaustive′⇔NonExhaustive = mk⇔ NonExhaustive′→NonExhaustive NonExhaustive→NonExhaustive′

  Exhaustive→Exhaustive′ : Exhaustive P → Exhaustive′ P
  Exhaustive→Exhaustive′ exh (vs , P⋠vs , _) = P⋠vs (toAny (exh vs))

  Exhaustive′→Exhaustive : Exhaustive′ P → Exhaustive P
  Exhaustive′→Exhaustive exh vs with match? P vs
  ... | yes P≼vs = P≼vs
  ... | no P⋠vs = contradiction (vs , ¬First⇒¬Any id P⋠vs , ∙*≼ ) exh

  -- The two definitions of exhaustiveness are equivalent
  Exhaustive′⇔Exhaustive : Exhaustive′ P ⇔ Exhaustive P
  Exhaustive′⇔Exhaustive = mk⇔ Exhaustive′→Exhaustive Exhaustive→Exhaustive′

--------------------------------------------------------------------------------

-- Set of root constructors of a pattern
rootCons : Pat α → ConSet α
rootCons ∙ = ⊥
rootCons (con c _) = ⁅ c ⁆
rootCons (p ∣ q) = rootCons p ∪ rootCons q

-- Set of root constructors in the first column of a pattern matrix
Σ : PatMat (α ∷ αs) → ConSet α
Σ = ⋃ ∘ List.map (rootCons ∘ All.head)

emptyRootCons? : (p : Pat α) → Dec (Empty (rootCons p))
emptyRootCons? ∙ = yes (∉⊥ ∘ proj₂)
emptyRootCons? (con c _) = no λ empty⁅c⁆ → empty⁅c⁆ (c , x∈⁅x⁆ c)
emptyRootCons? (p ∣ q) = Dec.map Empty∪⇔ (emptyRootCons? p ×-dec emptyRootCons? q)

emptyΣ? : (P : PatMat (α ∷ αs)) → Dec (Empty (Σ P))
emptyΣ? [] = yes (∉⊥ ∘ proj₂)
emptyΣ? (ps ∷ P) = Dec.map Empty∪⇔ (emptyRootCons? (All.head ps) ×-dec emptyΣ? P)

∃missingCon? : (P : PatMat (α ∷ αs)) → Dec (∃[ c ] c ∉ Σ P)
∃missingCon? {α = α} P with emptyΣ? P
... | yes emptyΣ = yes (inhabCon α , emptyΣ ∘ (inhabCon α ,_))
... | no _ =
      Dec.map′
        (Product.map₂ x∈∁p⇒x∉p)
        (Product.map₂ x∉p⇒x∈∁p)
        (nonempty? (∁ (Σ P)))
{-
-- The above definition has better decidability than the following one;
-- When α is abstract, you can't decide how many constructors there are in α, therefore you can't decide if there is a missing constructor.
-- The definition above exploits the fact that you can decide if the set is empty without knowing the number of constructors.

∃missingCon? =
  Dec.map′ (Product.map₂ x∈∁p⇒x∉p) (Product.map₂ x∉p⇒x∈∁p) (nonempty? (∁ (Σ P)))
-}

-- Specialization: filters out clauses whose first pattern does not match a value of the form `con c -`.
𝒮-aux : ∀ c → Pats (α ∷ αs) → List (Pats (args α c ++ αs))
𝒮-aux c (∙ ∷ ps) = All.++⁺ ∙* ps ∷ []
𝒮-aux c (con d rs ∷ ps) with c Fin.≟ d
... | no _ = []
... | yes refl = All.++⁺ rs ps ∷ []
𝒮-aux c (r₁ ∣ r₂ ∷ ps) = 𝒮-aux c (r₁ ∷ ps) ++ 𝒮-aux c (r₂ ∷ ps)

𝒮 : ∀ c → PatMat (α ∷ αs) → PatMat (args α c ++ αs)
𝒮 = concatMap ∘ 𝒮-aux

-- Default matrix: filters out clauses whose first pattern is a constructor pattern
𝒟-aux : Pats (α ∷ αs) → List (Pats αs)
𝒟-aux (∙ ∷ ps) = ps ∷ []
𝒟-aux (con _ _ ∷ ps) = []
𝒟-aux (r₁ ∣ r₂ ∷ ps) = 𝒟-aux (r₁ ∷ ps) ++ 𝒟-aux (r₂ ∷ ps)

𝒟 : PatMat (α ∷ αs) → PatMat αs
𝒟 = concatMap 𝒟-aux

--------------------------------------------------------------------------------

-- [] is useful wrt []
useful-[]-[] : Useful [] []
useful-[]-[] = [] , ¬Any[] , []

-- [] is not wrt any non-empty matrix
¬useful-∷-[] : ∀ {P ps} → ¬ Useful (ps ∷ P) []
¬useful-∷-[] {ps = []} ([] , []P⋠[] , _) = []P⋠[] (here [])

module _ {r₁ r₂ : Pat α} {ps : Pats αs} {P} where

  useful-∣⁺ : Useful P (r₁ ∷ ps) ⊎ Useful P (r₂ ∷ ps) → Useful P (r₁ ∣ r₂ ∷ ps)
  useful-∣⁺ (inj₁ (vvs , P⋠vvs , r₁≼v ∷ ps≼vs)) =
    vvs , P⋠vvs , ∣≼ˡ r₁≼v ∷ ps≼vs
  useful-∣⁺ (inj₂ (vvs , P⋠vvs , r₂≼v ∷ ps≼vs)) =
    vvs , P⋠vvs , ∣≼ʳ r₂≼v ∷ ps≼vs

  useful-∣⁻ : Useful P (r₁ ∣ r₂ ∷ ps) → Useful P (r₁ ∷ ps) ⊎ Useful P (r₂ ∷ ps)
  useful-∣⁻ (vvs , P⋠vvs , ∣≼ˡ r₁≼v ∷ ps≼vs) =
    inj₁ (vvs , P⋠vvs , r₁≼v ∷ ps≼vs)
  useful-∣⁻ (vvs , P⋠vvs , ∣≼ʳ r₂≼v ∷ ps≼vs) =
    inj₂ (vvs , P⋠vvs , r₂≼v ∷ ps≼vs)

  -- (r₁ ∣ r₂ ∷ ps) is useful wrt P iff (r₁ ∷ ps) or (r₂ ∷ ps) is useful wrt P
  useful-∣⇔ : (Useful P (r₁ ∷ ps) ⊎ Useful P (r₂ ∷ ps)) ⇔ Useful P (r₁ ∣ r₂ ∷ ps)
  useful-∣⇔ = mk⇔ useful-∣⁺ useful-∣⁻


module _ {c} {us : Vals (args α c)} {vs : Vals αs} where

  𝒮-aux-pres-≼ : ∀ {ps}
    → ps ≼* con {α} c us ∷ vs
    → 𝒮-aux c ps ≼** All.++⁺ us vs
  𝒮-aux-pres-≼ {∙ ∷ ps} ∙ps≼cusvs = here (∙≼*⁻ ∙ps≼cusvs)
  𝒮-aux-pres-≼ {con d rs ∷ ps} drsps≼cusvs with c Fin.≟ d
  ... | no c≢d = contradiction (sym (c≼d→c≡d (∷⁻ drsps≼cusvs .proj₁))) c≢d
  ... | yes refl = here (con≼*⁻ drsps≼cusvs)
  𝒮-aux-pres-≼ {r₁ ∣ r₂ ∷ ps} =
    [ Any.++⁺ˡ , Any.++⁺ʳ _ ] ∘ Sum.map 𝒮-aux-pres-≼ 𝒮-aux-pres-≼ ∘ ∣≼*⁻

  -- 𝒮 preserves ≼
  𝒮-pres-≼ : ∀ {P}
    → P ≼** con {α} c us ∷ vs
    → 𝒮 c P ≼** All.++⁺ us vs
  𝒮-pres-≼ = Any.concat⁺ ∘ Any.gmap 𝒮-aux-pres-≼

  𝒮-aux-pres-≼⁻ : ∀ {ps}
    → 𝒮-aux c ps ≼** All.++⁺ us vs
    → ps ≼* con {α} c us ∷ vs
  𝒮-aux-pres-≼⁻ {∙ ∷ ps} (here ∙*ps≼usvs) = ∙≼*⁺ ∙*ps≼usvs
  𝒮-aux-pres-≼⁻ {con d rs ∷ ps} _ with c Fin.≟ d
  𝒮-aux-pres-≼⁻ {con d rs ∷ ps} (here drsps≼cusvs) | yes refl = con≼*⁺ drsps≼cusvs
  𝒮-aux-pres-≼⁻ {r₁ ∣ r₂ ∷ ps} =
    ∣≼*⁺ ∘ Sum.map 𝒮-aux-pres-≼⁻ 𝒮-aux-pres-≼⁻ ∘ Any.++⁻ _

  -- "Unspecializing" preserves ≼
  𝒮-pres-≼⁻ : ∀ {P}
    → 𝒮 c P ≼** All.++⁺ us vs
    → P ≼** con {α} c us ∷ vs
  𝒮-pres-≼⁻ = Any.map 𝒮-aux-pres-≼⁻ ∘ Any.map⁻ ∘ Any.concat⁻ _

  𝒮-pres-≼⇔ : ∀ {P}
    → P ≼** con {α} c us ∷ vs ⇔ 𝒮 c P ≼** All.++⁺ us vs
  𝒮-pres-≼⇔ = mk⇔ 𝒮-pres-≼ 𝒮-pres-≼⁻


module _ {c} {rs : Pats (args α c)} {ps : Pats αs} {P : PatMat (α ∷ αs)} where

  useful-con⁺ : Useful (𝒮 c P) (All.++⁺ rs ps) → Useful P (con c rs ∷ ps)
  useful-con⁺ (usvs , 𝒮P⋠usvs , rsps≼usvs)
    with us , vs , refl , rs≼us , ps≼vs ← split rs rsps≼usvs =
    con c us ∷ vs , contraposition 𝒮-pres-≼ 𝒮P⋠usvs , con≼ rs≼us ∷ ps≼vs

  useful-con⁻ : Useful P (con c rs ∷ ps) → Useful (𝒮 c P) (All.++⁺ rs ps)
  useful-con⁻ (con c vs ∷ us , P⋠cvsus , con≼ rs≼vs ∷ ps≼us) =
    All.++⁺ vs us , contraposition 𝒮-pres-≼⁻ P⋠cvsus , ++⁺ rs≼vs ps≼us

  -- con c rs ∷ ps is useful wrt P iff rs ++ ps is useful wrt 𝒮 c P
  useful-con⇔ : Useful (𝒮 c P) (All.++⁺ rs ps) ⇔ Useful P (con c rs ∷ ps)
  useful-con⇔ = mk⇔ useful-con⁺ useful-con⁻


module _ {α αs} {ps : Pats αs} {P} where

  -- If there exists a constructor c such that `∙* ++ ps` is useful wrt `𝒮 c P`, `∙ ∷ ps` is also useful wrt P
  useful-∙-𝒮⁺ : ∃[ c ] Useful (𝒮 c P) (All.++⁺ ∙* ps) → Useful P (∙ {α} ∷ ps)
  useful-∙-𝒮⁺ (c , usvs , 𝒮P⋠usvs , ∙*ps≼usvs)
    with us , vs , refl , _ , ps≼vs ← split {args α c} ∙* ∙*ps≼usvs =
    con c us ∷ vs , contraposition 𝒮-pres-≼ 𝒮P⋠usvs , ∙≼ ∷ ps≼vs

  -- If `∙ ∷ ps` is useful wrt P, there exists a constructor c such that `∙* ++ ps` is useful wrt `𝒮 c P`
  useful-∙-𝒮⁻ : Useful P (∙ {α} ∷ ps) → ∃[ c ] Useful (𝒮 c P) (All.++⁺ ∙* ps)
  useful-∙-𝒮⁻ (con c us ∷ vs , P⋠cusvs , ∙≼ ∷ ps≼vs) =
    c , All.++⁺ us vs , contraposition 𝒮-pres-≼⁻ P⋠cusvs , ++⁺ ∙*≼ ps≼vs

  -- ∙ ∷ ps is useful wrt P iff ∙* ++ ps is useful wrt 𝒮 c P
  useful-∙-𝒮⇔ : (∃[ c ] Useful (𝒮 c P) (All.++⁺ ∙* ps)) ⇔ Useful P (∙ {α} ∷ ps)
  useful-∙-𝒮⇔ = mk⇔ useful-∙-𝒮⁺ useful-∙-𝒮⁻


module _ {c} {us : Vals (args α c)} {vs : Vals αs} where

  𝒟-aux-pres-≼ : ∀ {ps}
    → c ∉ rootCons (All.head ps)
    → ps ≼* con {α} c us ∷ vs
    → 𝒟-aux ps ≼** vs
  𝒟-aux-pres-≼ {∙ ∷ ps} _ ∙ps≼cusvs = here (∷⁻ ∙ps≼cusvs .proj₂)
  𝒟-aux-pres-≼ {con d rs ∷ ps} c∉⁅d⁆ drsps≼cusvs =
    contradiction (Equivalence.from x∈⁅y⁆⇔x≡y (sym (c≼d→c≡d (∷⁻ drsps≼cusvs .proj₁)))) c∉⁅d⁆
  𝒟-aux-pres-≼ {r₁ ∣ r₂ ∷ ps} c∉Σr₁∪r₂ =
    [ Any.++⁺ˡ , Any.++⁺ʳ _ ] ∘
    Sum.map (𝒟-aux-pres-≼ (x∉p∪q⁻ˡ c∉Σr₁∪r₂)) (𝒟-aux-pres-≼ (x∉p∪q⁻ʳ c∉Σr₁∪r₂)) ∘
    ∣≼*⁻

  -- If c is not in Σ P, 𝒟 preserves ≼
  𝒟-pres-≼ : ∀ {P}
    → c ∉ Σ P
    → P ≼** con {α} c us ∷ vs
    → 𝒟 P ≼** vs
  𝒟-pres-≼ {[]} _ ()
  𝒟-pres-≼ {ps ∷ P} c∉Σps∪P (here ps≼cusvs) =
    Any.++⁺ˡ (𝒟-aux-pres-≼ (x∉p∪q⁻ˡ c∉Σps∪P) ps≼cusvs)
  𝒟-pres-≼ {ps ∷ P} c∉Σps∪P (there P≼cusvs) =
    Any.++⁺ʳ _ (𝒟-pres-≼ (x∉p∪q⁻ʳ c∉Σps∪P) P≼cusvs)


module _ {v : Val α} {vs : Vals αs} where

  𝒟-aux-pres-≼⁻ : ∀ {ps} → 𝒟-aux ps ≼** vs → ps ≼* v ∷ vs
  𝒟-aux-pres-≼⁻ {∙ ∷ ps} (here ∙ps≼vvs) = ∙≼ ∷ ∙ps≼vvs
  𝒟-aux-pres-≼⁻ {r₁ ∣ r₂ ∷ ps} =
    ∣≼*⁺ ∘ Sum.map 𝒟-aux-pres-≼⁻ 𝒟-aux-pres-≼⁻ ∘ Any.++⁻ _

  -- The "inverse" of 𝒟 preserves ≼ (with no condition on v unlike 𝒟-pres-≼)
  𝒟-pres-≼⁻ : ∀ {P} → 𝒟 P ≼** vs → P ≼** v ∷ vs
  𝒟-pres-≼⁻ = Any.map 𝒟-aux-pres-≼⁻ ∘ Any.map⁻ ∘ Any.concat⁻ _


module _ {α} {ps : Pats αs} {P} where

  -- If Σ P is not complete, and ps is useful wrt 𝒟 P, ∙ ∷ ps is also useful wrt P.
  -- That means, it suffices to check for usefulness of ps wrt 𝒟 P if Σ P is not complete.
  useful-∙-𝒟⁺ :
      ∃[ c ] c ∉ Σ P
    → Useful (𝒟 P) ps
    → Useful P (∙ {α} ∷ ps)
  useful-∙-𝒟⁺ (c , c∉ΣP) (vs , 𝒟P⋠vs , ps≼vs) =
    inhabOf c ∷ vs , contraposition (𝒟-pres-≼ c∉ΣP) 𝒟P⋠vs , ∙≼ ∷ ps≼vs

  -- ps is useful wrt (𝒟 P) if (∙ ∷ ps) is useful wrt P
  useful-∙-𝒟⁻ : Useful P (∙ {α} ∷ ps) → Useful (𝒟 P) ps
  useful-∙-𝒟⁻ (v ∷ vs  , P⋠vvs , ∙≼ ∷ ps≼vs) =
    vs , contraposition 𝒟-pres-≼⁻ P⋠vvs , ps≼vs

--------------------------------------------------------------------------------
-- Usefulness checking algorithm

data UsefulAcc : PatMat αs → Pats αs → Set where
  stop-[] : ∀ {P} → UsefulAcc P []
  step-∙ : ∀ {P : PatMat (α ∷ αs)} {ps}
    → UsefulAcc (𝒟 P) ps
    → (∀ {c} → UsefulAcc (𝒮 c P) (All.++⁺ ∙* ps))
    → UsefulAcc P (∙ ∷ ps)
  step-con : ∀ {c} {P} {rs : Pats (args α c)} {ps : Pats αs}
    → UsefulAcc (𝒮 c P) (All.++⁺ rs ps)
    → UsefulAcc P (con {α} c rs ∷ ps)
  step-∣ : ∀ {P} {r₁ r₂ : Pat α} {ps : Pats αs}
    → UsefulAcc P (r₁ ∷ ps)
    → UsefulAcc P (r₂ ∷ ps)
    → UsefulAcc P (r₁ ∣ r₂ ∷ ps)

useful?-aux : ∀ (P : PatMat αs) ps
  → UsefulAcc P ps
  → Dec (Useful P ps)
useful?-aux [] [] stop-[] = yes useful-[]-[]
useful?-aux (_ ∷ _) [] stop-[] = no ¬useful-∷-[]
useful?-aux P (∙ ∷ ps) (step-∙ hs₁ hs₂) with ∃missingCon? P
... | yes ∃c∉ΣP =
      Dec.map′ (useful-∙-𝒟⁺ ∃c∉ΣP) useful-∙-𝒟⁻ (useful?-aux (𝒟 P) ps hs₁)
... | no _ =
      Dec.map useful-∙-𝒮⇔ (any? λ c → useful?-aux (𝒮 c P) (All.++⁺ ∙* ps) hs₂)
useful?-aux P (con c rs ∷ ps) (step-con hs) =
  Dec.map useful-con⇔ (useful?-aux (𝒮 c P) (All.++⁺ rs ps) hs)
useful?-aux P (r₁ ∣ r₂ ∷ ps) (step-∣ hs₁ hs₂) =
  Dec.map
    useful-∣⇔
    (useful?-aux P (r₁ ∷ ps) hs₁ ⊎-dec useful?-aux P (r₂ ∷ ps) hs₂)

--------------------------------------------------------------------------------
-- The usefulness checking algorithm is terminating

patSize patSize′ : Pat α → ℕ
patsSize : Pats αs → ℕ

patSize p = suc (patSize′ p)
-- patSize′ returns the size of a pattern *minus 1*.
-- Now it is obvious that the patSize is greater than 0.
patSize′ ∙ = 0
patSize′ (con c ps) = patsSize ps
patSize′ (p ∣ q) = suc (patSize′ p + patSize′ q)

patsSize [] = 0
patsSize (p ∷ ps) = patSize p + patsSize ps

patsSize-++ : (ps : Pats αs) (qs : Pats βs)
  → patsSize (All.++⁺ ps qs) ≡ patsSize ps + patsSize qs
patsSize-++ [] qs = refl
patsSize-++ (p ∷ ps) qs rewrite patsSize-++ ps qs = sym (+-assoc (patSize p) _ _)

lem1 : ∀ c (rs : Pats (args α c)) (ps : Pats βs)
  → patsSize (All.++⁺ rs ps) <′ patsSize (con {α} c rs ∷ ps)
lem1 c ps qs rewrite patsSize-++ ps qs = <′-base

lem2 : ∀ (r₁ r₂ : Pat α) (ps : Pats αs)
  → patsSize (r₁ ∷ ps) <′ patsSize (r₁ ∣ r₂ ∷ ps)
lem2 r₁ r₂ ps
  rewrite cong (_+ patsSize ps) (+-comm (patSize′ r₁) (patSize′ r₂))
  rewrite +-assoc (patSize′ r₂) (patSize′ r₁) (patsSize ps) =
  s≤′s (s≤′s (≤⇒≤′ (m≤n+m _ (patSize′ r₂))))

lem3 : ∀ (r₁ r₂ : Pat α) (ps : Pats αs)
  → patsSize (r₂ ∷ ps) <′ patsSize (r₁ ∣ r₂ ∷ ps)
lem3 r₁ r₂ ps
  rewrite +-assoc (patSize′ r₁) (patSize′ r₂) (patsSize ps) =
  s≤′s (s≤′s (≤⇒≤′ (m≤n+m _ (patSize′ r₁))))

∀usefulAcc-aux : ∀ (P : PatMat αs) ps
  → Acc _<′_ (patsSize ps)
  → UsefulAcc P ps
∀usefulAcc-aux P [] (acc rs) = stop-[]
∀usefulAcc-aux P (∙ ∷ ps) (acc hs) =
  step-∙
    (∀usefulAcc-aux (𝒟 P) ps (hs <′-base))
    {!   !}
∀usefulAcc-aux {α ∷ _} P (con c rs ∷ ps) (acc hs) =
  step-con (∀usefulAcc-aux (𝒮 c P) (All.++⁺ rs ps) (hs (lem1 {α} c rs ps)))
∀usefulAcc-aux P (r₁ ∣ r₂ ∷ ps) (acc hs) =
  step-∣
    (∀usefulAcc-aux P (r₁ ∷ ps) (hs (lem2 r₁ r₂ ps)))
    (∀usefulAcc-aux P (r₂ ∷ ps) (hs (lem3 r₁ r₂ ps)))

∀usefulAcc : ∀ (P : PatMat αs) ps → UsefulAcc P ps
∀usefulAcc P ps = ∀usefulAcc-aux P ps (<′-wellFounded (patsSize ps))

--------------------------------------------------------------------------------

useful? : ∀ (P : PatMat αs) ps → Dec (Useful P ps)
useful? P ps = useful?-aux P ps (∀usefulAcc P ps)

exhaustive? : (P : PatMat αs) → Exhaustive P ⊎ NonExhaustive P
exhaustive? P with useful? P ∙*
... | yes h = inj₂ (NonExhaustive′→NonExhaustive h)
... | no h = inj₁ (Exhaustive′→Exhaustive h)
