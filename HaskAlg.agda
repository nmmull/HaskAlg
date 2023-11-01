module HaskAlg where

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

record Functor₁ (F : Set → Set) : Set₁ where
  field
    fmap : Fmap F
    fmap-id : Fmap-id fmap

record Functor₂ (F : Set → Set) : Set₁ where
  field
    fmap : Fmap F
    fmap-id : Fmap-id fmap
    fmap-comp : Fmap-comp fmap

F₂→F₁ : ∀ {F} → Functor₂ F → Functor₁ F
F₂→F₁ isFun = record { fmap = fmap ; fmap-id = fmap-id } where
  fmap = Functor₂.fmap isFun
  fmap-id = Functor₂.fmap-id isFun

F₁→F₂ : ∀ {F} → Functor₁ F → Functor₂ F
F₁→F₂ Fun = record { fmap = fmap ; fmap-id = fmap-id ; fmap-comp = fmap-comp } where
  fmap = Functor₁.fmap Fun
  fmap-id = Functor₁.fmap-id Fun
  fmap-comp = Fid→Fcomp fmap fmap-id

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
