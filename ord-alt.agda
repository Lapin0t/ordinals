module ord-alt where

data ⊥ : Set where
record ⊤ : Set where constructor *

data bool : Set where tt ff : bool

data _∨_ (A B : Set) : Set where
  inl : A → A ∨ B
  inr : B → A ∨ B

¬_ : Set → Set
¬ A = A → ⊥

infix 15 _≺_
infix 15 _≼_

data ord : Set₁ where
  su : ord → ord
  lu : {A : Set} → (A → ord) → ord

data _≼_ : ord → ord → Set
data _≺_ : ord → ord → Set

data _≼_ where
  s≼α : ∀ {α β} → α ≺ β → su α ≼ β
  l≼α : ∀ {A φ α} → ((a : A) → φ a ≼ α) → lu φ ≼ α
  α≼l : ∀ {A φ α} (a : A) → α ≼ φ a → α ≼ lu φ
  wkn : ∀ {α β} → α ≺ β → α ≼ β

data _≺_ where
  α≺s : ∀ {α β} → α ≼ β → α ≺ su β
  α≺l : ∀ {A φ α} (a : A) → α ≺ φ a → α ≺ lu φ

norm-l : ∀ {A φ α} → lu φ ≼ α → (a : A) → φ a ≼ α
norm'-l : ∀ {A φ α} → lu φ ≺ α → (a : A) → φ a ≺ α

norm-l (l≼α x) a = x a
norm-l (α≼l a₁ x) a = α≼l a₁ (norm-l x a)
norm-l (wkn (α≺s x)) a = wkn (α≺s (norm-l x a))
norm-l (wkn (α≺l a₁ x)) a = wkn (α≺l a₁ (norm'-l x a))

norm'-l (α≺s (l≼α x)) a = α≺s (x a)
norm'-l (α≺s (α≼l a₁ x)) a = α≺s (α≼l a₁ (norm-l x a))
norm'-l (α≺s (wkn x)) a = α≺s (wkn (norm'-l x a))
norm'-l (α≺l a₁ x) a = α≺l a₁ (norm'-l x a)

norm-s : ∀ {α β} → su α ≼ β → α ≺ β
norm-s (s≼α x) = x
norm-s (α≼l a x) = α≺l a (norm-s x)
norm-s (wkn (α≺s x)) = α≺s (wkn (norm-s x))
norm-s (wkn (α≺l a x)) = α≺l a (norm-s (wkn x))

trans : ∀ {α β γ} → α ≼ β → β ≼ γ → α ≼ γ
trans-≺₀ : ∀ {α β γ} → α ≼ β → β ≺ γ → α ≺ γ
trans-≺₁ : ∀ {α β γ} → α ≺ β → β ≼ γ → α ≺ γ

trans (s≼α x)   y = s≼α (trans-≺₁ x y)
trans (l≼α x)   y = l≼α (λ a → trans (x a) y)
trans (α≼l a x) y = trans x (norm-l y a)
trans (wkn x)   y = wkn (trans-≺₁ x y)

trans-≺₀ x (α≺s y) = α≺s (trans x y)
trans-≺₀ x (α≺l a y) = α≺l a (trans-≺₀ x y)

trans-≺₁ (α≺s x) (s≼α y) = trans-≺₀ x y
trans-≺₁ (α≺l a x) (l≼α f) = trans-≺₁ x (f a)
trans-≺₁ (α≺s x) (α≼l a y) = α≺l a (trans-≺₁ (α≺s x) y)
trans-≺₁ (α≺l a x) (α≼l b y) = trans-≺₁ x (α≼l b (norm-l y a))
trans-≺₁ x (wkn (α≺s y)) = α≺s (wkn (trans-≺₁ x y))
trans-≺₁ x (wkn (α≺l a y)) = α≺l a (trans-≺₁ x (wkn y))

irr : ∀ {α} → ¬ (α ≺ α)
irr (α≺s x)   = irr (norm-s x)
irr (α≺l a x) = irr (norm'-l x a)

lem₀ : ∀ {α β} → α ≼ β → ¬ (β ≺ α)
lem₀ x y = irr (trans-≺₀ x y)

lem₁ : ∀ {α β} → α ≺ β → ¬ (β ≼ α)
lem₁ x y = irr (trans-≺₁ x y)

_⊔_ : ord → ord → ord
α ⊔ β = lu {bool} λ { tt → α ; ff → β }

ze : ord
ze = lu {⊥} λ ()

z≼α : ∀ {α} → ze ≼ α
z≼α = l≼α (λ ())

_+_ : ord → ord → ord
α + su β = su (α + β)
α + lu {A} φ = lu {⊤ ∨ A} λ { (inl *) → α; (inr x) → α + φ x }


