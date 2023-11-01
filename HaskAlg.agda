module HaskAlg where

open import Data.Product using (_×_; proj₁; proj₂; _,_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)


postulate
  f-ext : ∀ {a b : Set} {f g : a → b} →
    (∀ {x} → f x ≡ g x) → f ≡ g

id : {a : Set} → a → a
id x = x

infixr 9 _∘_
_∘_ : {a b c : Set} → (b → c) → (a → b) → a → c
(f ∘ g) x = f (g x)

id∘f≡f : ∀ {a b} {f : a → b} →
  id ∘ f ≡ f
id∘f≡f = f-ext refl

Fmap : (F : Set → Set) → Set₁
Fmap F = {a b : Set} → (a → b) → F a → F b

postulate
  free₁ :
    ∀ {F} {a b c d}
    {f : b → c} {g : a → b} {h : d → c} {j : a → d} →
    (fmap : Fmap F) →
    f ∘ g ≡ h ∘ j →
    fmap f ∘ fmap g ≡ fmap h ∘ fmap j

Fmap-id : ∀ {F : Set → Set} → (fmap : Fmap F) → Set₁
Fmap-id {F} fmap = ∀ {a} → fmap {a} id ≡ id {F _}

Fmap-comp : ∀ {F} → (fmap : Fmap F) → Set₁
Fmap-comp fmap =
  ∀ {a b c f g} →
  fmap {a} {c} (f ∘ g) ≡ fmap {b} f ∘ fmap g

Fid→Fcomp : ∀ {F} → (fmap : Fmap F) →
  Fmap-id fmap → Fmap-comp fmap
Fid→Fcomp fmap id-prf {f = f} {g = g} =
  begin
    fmap (f ∘ g)
  ≡⟨ id∘f≡f ⟩
    id ∘ fmap (f ∘ g)
  ≡⟨ cong (λ h → h ∘ fmap (f ∘ g)) (sym id-prf) ⟩
    fmap id ∘ fmap (f ∘ g)
  ≡⟨ free₁ fmap id∘f≡f ⟩
    fmap f ∘ fmap g
  ∎

isFunctorial₁ : ∀ {F} (fmap : Fmap F) → Set₁
isFunctorial₁ fmap = Fmap-id fmap

isFunctorial₂ : ∀ {F} (fmap : Fmap F) → Set₁
isFunctorial₂ fmap = Fmap-id fmap × Fmap-comp fmap

isF₂→isF₁ : ∀ {F} (fmap : Fmap F) → isFunctorial₂ fmap → isFunctorial₁ fmap
isF₂→isF₁ fmap = proj₁

isF₁→isF₂ : ∀ {F} (fmap : Fmap F) → isFunctorial₁ fmap → isFunctorial₂ fmap
isF₁→isF₂ fmap prf = prf , Fid→Fcomp fmap prf

Pure : (F : Set → Set) → Set₁
Pure F = {a : Set} → a → F a

App : (F : Set → Set) → Set₁
App F = {a b : Set} → F (a → b) → F a → F b

App-id : ∀ {F} → Pure F → App F → Set₁
App-id {F} pure _<*>_ = ∀ {a} {v : F a} →
  pure id <*> v ≡ v

App-hom : ∀ {F} → Pure F → App F → Set₁
App-hom pure _<*>_ = ∀ {a b} {f : a → b} {x : a} →
  pure f <*> pure x ≡ pure (f x)
