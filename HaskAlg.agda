module HaskAlg where

open import Data.Product using (_×_; proj₁; proj₂; _,_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

--------------------------------------------------
-- Signature

Fmap : (F : Set → Set) → Set₁
Fmap F = {a b : Set} → (a → b) → F a → F b

Pure : (F : Set → Set) → Set₁
Pure F = {a : Set} → a → F a

App : (F : Set → Set) → Set₁
App F = {a b : Set} → F (a → b) → F a → F b

--------------------------------------------------
-- Basics

variable
  a b c d : Set
  f f₁ f₂ : b → c

postulate
  f-ext : (∀ {x} → f₁ x ≡ f₂ x) → f₁ ≡ f₂

id : a → a
id x = x

infixr 9 _∘_
_∘_ : (b → c) → (a → b) → a → c
_∘_ f g x = f (g x)

id∘f≡f : id ∘ f ≡ f
id∘f≡f = f-ext refl

--------------------------------------------------
-- Axioms

variable
  F : Set → Set

-- Functor Laws

Fmap-id : Fmap F → Set₁
Fmap-id fmap = ∀ {a} →
  fmap {a} id ≡ id

Fmap-comp : Fmap F → Set₁
Fmap-comp fmap = ∀ {a b c} {f : b → c} {g : a → b} →
  fmap (f ∘ g) ≡ fmap f ∘ fmap g

Free : Fmap F → Set₁
Free fmap = ∀ {a b c d f j} {g : a → b} {h : d → c} →
  f ∘ g ≡ h ∘ j →
  fmap f ∘ fmap g ≡ fmap h ∘ fmap j

-- Applicative Laws

App-id : Pure F → App F → Set₁
App-id {F = F} pure _<*>_ = ∀ {a} {v : F a} →
  pure id <*> v ≡ v

App-comp : Pure F → App F → Set₁
App-comp {F = F} pure _<*>_ = ∀ {a b c w} {u : F (b → c)} {v : F (a → b)} →
  ((pure _∘_ <*> u) <*> v) <*> w ≡ u <*> (v <*> w)

App-hom : Pure F → App F → Set₁
App-hom pure _<*>_ = ∀ {a b x} {f : a → b} →
  pure f <*> pure x ≡ pure (f x)

App-inter : Pure F → App F → Set₁
App-inter {F} pure _<*>_ = ∀ {a b y} {u : F (a → b)} →
  u <*> pure y ≡ pure (λ f → f y) <*> u

Fmap-App : Fmap F → Pure F → App F → Set₁
Fmap-App fmap pure _<*>_ = ∀ {a b x} {f : a → b} →
  fmap f x ≡ pure f <*> x

-- Structures

isFunc : Fmap F → Set₁
isFunc fmap = Fmap-id fmap × Fmap-comp fmap

isApp : Fmap F → Pure F → App F → Set₁
isApp fmap pure app =
  isFunc fmap ×
  App-comp pure app ×
  App-hom pure app ×
  App-inter pure app

--------------------------------------------------
-- Theorems

module Theorems
  (fmap : Fmap F)
  (pure : Pure F)
  (app : App F) where

  infixr 20 _<*>_
  _<*>_ : App F
  _<*>_ = app

  Fid+Free→Fcomp : Fmap-id fmap → Free fmap → Fmap-comp fmap
  Fid+Free→Fcomp id-prf free-prf {f = f} {g = g} =
    begin
      fmap (f ∘ g)
    ≡⟨ id∘f≡f ⟩
      id ∘ fmap (f ∘ g)
    ≡⟨ cong (λ h → h ∘ fmap (f ∘ g)) (sym id-prf) ⟩
      fmap id ∘ fmap (f ∘ g)
    ≡⟨ free-prf id∘f≡f ⟩
      fmap f ∘ fmap g
    ∎

  Fcomp→Free : Fmap-comp fmap → Free fmap
  Fcomp→Free comp-prf {f = f} {j = j} {g = g} {h = h} eq =
    begin
      fmap f ∘ fmap g
    ≡⟨ sym comp-prf ⟩
      fmap (f ∘ g)
    ≡⟨ cong fmap eq ⟩
      fmap (h ∘ j)
    ≡⟨ comp-prf ⟩
      fmap h ∘ fmap j
    ∎

  isApp→Fmap-App : isApp fmap pure _<*>_ → Fmap-App fmap pure _<*>_
  isApp→Fmap-App ((id-prf , fcomp-prf) , (acomp-prf , hom-prf , inter-prf)) = {!!}
