
open import Data.List
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Product
open import Data.Sum

data _▶_≡_ {A : Set}(x : A) : List A → List A → Set where
  here  : ∀ {xs} → x ▶ xs ≡ (x ∷ xs)
  there : ∀ {y xs ys} → x ▶ xs ≡ ys → x ▶ (y ∷ xs) ≡ (y ∷ ys)

data Perm {A : Set} (xs : List A) : List A → Set where
  refl : Perm xs xs
  ins  : ∀ {x ys xs' ys'} → Perm xs' ys' → x ▶ xs' ≡ xs → x ▶ ys' ≡ ys → Perm xs ys

▶-inv :
  ∀ {A}{a : A}{b as bs cs}
  → a ▶ as ≡ cs
  → b ▶ bs ≡ cs
  → (a ≡ b × as ≡ bs) ⊎ (∃ λ ds → b ▶ ds ≡ as × a ▶ ds ≡ bs)
▶-inv here here = inj₁ (refl , refl)
▶-inv here (there p2) = inj₂ (_ , p2 , here)
▶-inv (there p1) here = inj₂ (_ , here , p1)
▶-inv (there p1) (there p2) with ▶-inv p1 p2
... | inj₁ (refl , refl) = inj₁ (refl , refl)
... | inj₂ (ds , ias , ibs) = inj₂ (_ ∷ ds , there ias , there ibs)

▶-exch :
  ∀ {A}{x : A}{y xs xxs yxxs}
  → x ▶ xs ≡ xxs → y ▶ xxs ≡ yxxs → ∃ λ yxs → (y ▶ xs ≡ yxs) × (x ▶ yxs ≡ yxxs)
▶-exch p1 here = _ , here , there p1
▶-exch here (there p2) = _ , p2 , here
▶-exch (there p1) (there p2) with ▶-exch p1 p2
... | _ , p1' , p2' = _ , there p1' , there p2'

l1 : ∀ {A x xs xys} → Perm {A} (x ∷ xs) xys → ∃ λ ys → x ▶ ys ≡ xys × Perm xs ys
l1 refl = _ , here , refl
l1 (ins p here iys) = _ , iys , p
l1 (ins p (there ixs) iys) with l1 p
l1 {x = x}(ins {x = y}p (there ixs) iys) | ys , i , perm with ▶-exch i iys
l1 (ins p (there ixs) iys) | ys , i , perm | proj1 , proj2 , proj3
  = proj1 , proj3 , ins perm ixs proj2

▶-len : ∀ {A}{x : A}{xs ys} → x ▶ xs ≡ ys → suc (length xs) ≡ length ys
▶-len here = refl
▶-len (there p) rewrite ▶-len p = refl

extract-perm :
  ∀ {A x xs xys xxs}
  → (l : ℕ)
  → length xxs ≡ l
  → x ▶ xs ≡ xxs
  → Perm {A} xxs xys
  → ∃ λ ys → (x ▶ ys ≡ xys) × (Perm xs ys)
extract-perm zero () here p2
extract-perm zero () (there p1) p2
extract-perm (suc l) lp here refl = _ , here , refl
extract-perm (suc l) lp here (ins p2 here iys) = _ , iys , p2
extract-perm (suc l) lp here (ins p2 (there ixs) iys) with l1 p2
... | proj1 , proj2 , proj3 with ▶-exch proj2 iys
extract-perm (suc l) lp here (ins p2 (there ixs) iys) | proj1 , proj2 , proj6 | proj3 , proj4 , proj5
  = proj3 , proj5 , ins proj6 ixs proj4
extract-perm (suc l) lp (there p1) refl = _ , there p1 , refl
extract-perm (suc l) lp (there p1) (ins p2 here iys) with extract-perm l (cong pred lp) p1 p2
extract-perm (suc l) lp (there p1) (ins p2 here iys) | proj1 , proj2 , proj3 with ▶-exch proj2 iys
extract-perm (suc l) lp (there p1) (ins p2 here iys) | proj1 , proj2 , proj6 | proj3 , proj4 , proj5
  = proj3 , proj5 , ins proj6 here proj4
extract-perm (suc l) lp (there p1) (ins p2 (there ixs) iys) with ▶-inv p1 ixs
extract-perm (suc l) lp (there p1) (ins p2 (there ixs) iys) | inj₁ (refl , refl) = _ , iys , p2
extract-perm (suc l) lp (there p1) (ins p2 (there ixs) iys) | inj₂ (proj11 , proj12 , proj13) with l1 p2
extract-perm (suc zero) lp (there {y} {xs1} {[]} p1) (ins p2 (there ()) iys) | inj₂ (proj11 , proj12 , proj13) | proj21 , proj22 , proj23
extract-perm (suc zero) () (there {y} {xs1} {x1 ∷ ys} p1) (ins p2 (there ixs) iys) | inj₂ (proj11 , proj12 , proj13) | proj21 , proj22 , proj23
extract-perm (suc (suc l)) lp (there p1) (ins p2 (there ixs) iys) | inj₂ (proj11 , proj12 , proj13) | proj21 , proj22 , proj23 with extract-perm l (cong pred $ trans (▶-len ixs) (cong pred lp)) proj13 proj23
extract-perm (suc (suc l)) lp (there p1) (ins p2 (there ixs) iys) | inj₂ (proj11 , proj12 , proj13) | proj21 , proj22 , proj23 | proj31 , proj32 , proj33 with ▶-exch proj32 proj22
extract-perm (suc (suc l)) lp (there p1) (ins p2 (there ixs) iys) | inj₂ (proj11 , proj12 , proj13) | proj21 , proj22 , proj23 | proj31 , proj32 , proj33 | proj41 , proj42 , proj43 with ▶-exch proj43 iys
extract-perm (suc (suc l)) lp (there p1) (ins p2 (there ixs) iys) | inj₂ (proj11 , proj12 , proj13) | proj21 , proj22 , proj23 | proj31 , proj32 , proj33 | proj41 , proj42 , proj43 | proj51 , proj52 , proj53 = proj51 , proj53 , ins (ins proj33 here proj42) (there proj12) proj52

perm-sym : ∀ {A xs ys} → Perm {A} xs ys → Perm ys xs
perm-sym refl = refl
perm-sym (ins p ix iy) = ins (perm-sym p) iy ix

perm-trans : ∀ {A xs ys zs} → Perm {A} xs ys → Perm ys zs → Perm xs zs
perm-trans refl p2 = p2
perm-trans p1 refl = p1
perm-trans {ys = ys} (ins xy ix iy) p2 with extract-perm (length ys) refl iy p2
perm-trans (ins xy ix iy) p2 | proj1 , proj2 , proj3 = ins (perm-trans xy proj3) ix proj2
