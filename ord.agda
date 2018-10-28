module ord where

data nat : Set where
  ze : nat
  su : nat → nat

elim-nat : {A : Set} → A → (A → A) → nat → A
elim-nat x f ze = x
elim-nat x f (su n) = f (elim-nat x f n)

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

data _∨_ (A B : Set) : Set where
  inl : A → A ∨ B
  inr : B → A ∨ B

data dec (A : Set) : Set where
  yes : A → dec A
  no : ¬ A → dec A


infix 15 _≺_
infix 15 _≼_
infixl 20 _⊔_

data ord : Set
data _≼_ : ord → ord → Set
data _≺_ : ord → ord → Set

data ord where
  ze : ord
  su : ord → ord
  li : (φ : nat → ord) (u : (n : nat) → φ n ≺ φ (su n)) → ord
  _⊔_ : ord → ord → ord

data _≼_ where
  z≼α : ∀ {α} → ze ≼ α
  s≼α : ∀ {α β} → α ≺ β → su α ≼ β
  l≼α : ∀ {φ u α} → ((n : nat) → φ n ≼ α) → li φ u ≼ α
  ⊔≼α : ∀ {α β γ} → α ≼ γ → β ≼ γ → α ⊔ β ≼ γ
  wkn : ∀ {α β} → α ≺ β → α ≼ β

data _≺_ where
  α≺s : ∀ {α β} → α ≼ β → α ≺ su β
  α≺l : ∀ {φ u α} (n : nat) → α ≼ φ n → α ≺ li φ u
  α≺⊔₀ : ∀ {α β γ} → γ ≺ α → γ ≺ α ⊔ β
  α≺⊔₁ : ∀ {α β γ} → γ ≺ β → γ ≺ α ⊔ β

record _≃_ (α β : ord) : Set where
  field
    α≼β : α ≼ β
    β≼α : β ≼ α
open _≃_ public


--- Constructors alternate forms

α≼⊔₀ : ∀ {α β γ} → γ ≼ α → γ ≼ α ⊔ β
α≼⊔₀ z≼α         = z≼α
α≼⊔₀ (s≼α x)     = s≼α (α≺⊔₀ x)
α≼⊔₀ (l≼α x)     = l≼α (λ n → α≼⊔₀ (x n))
α≼⊔₀ (⊔≼α x₀ x₁) = ⊔≼α (α≼⊔₀ x₀) (α≼⊔₀ x₁)
α≼⊔₀ (wkn x)     = wkn (α≺⊔₀ x)

α≼⊔₁ : ∀ {α β γ} → γ ≼ β → γ ≼ α ⊔ β
α≼⊔₁ z≼α         = z≼α
α≼⊔₁ (s≼α x)     = s≼α (α≺⊔₁ x)
α≼⊔₁ (l≼α x)     = l≼α (λ n → α≼⊔₁ (x n))
α≼⊔₁ (⊔≼α x₀ x₁) = ⊔≼α (α≼⊔₁ x₀) (α≼⊔₁ x₁)
α≼⊔₁ (wkn x)     = wkn (α≺⊔₁ x)

s≼s : ∀ {α β} → α ≼ β → su α ≼ su β
s≼s x = s≼α (α≺s x)

s≺s : ∀ {α β} → α ≺ β → su α ≺ su β
s≺s x = α≺s (s≼α x)


module props where

  refl : ∀ {α} → α ≼ α
  refl {ze}     = z≼α
  refl {su _}   = s≼s refl
  refl {_ ⊔ _}  = ⊔≼α (α≼⊔₀ refl) (α≼⊔₁ refl)
  refl {li _ _} = l≼α (λ n → wkn (α≺l n refl))

  trans : ∀ {α β γ} → α ≼ β → β ≼ γ → α ≼ γ
  trans-≺₀ : ∀ {α β γ} → α ≼ β → β ≺ γ → α ≺ γ
  trans-≺₁ : ∀ {α β γ} → α ≺ β → β ≼ γ → α ≺ γ

  trans z≼α       y       = z≼α
  trans (wkn x)   y       = wkn (trans-≺₁ x y)
  trans x         (wkn y) = wkn (trans-≺₀ x y)
  trans (l≼α x)   y       = l≼α (λ n → trans (x n) y)
  trans (s≼α x)   y       = s≼α (trans-≺₁ x y)
  trans (⊔≼α a b) y       = ⊔≼α (trans a y) (trans b y)

  trans-≺₀ x (α≺s y)   = α≺s (trans x y)
  trans-≺₀ x (α≺l n y) = α≺l n (trans x y)
  trans-≺₀ x (α≺⊔₀ y)  = α≺⊔₀ (trans-≺₀ x y)
  trans-≺₀ x (α≺⊔₁ y)  = α≺⊔₁ (trans-≺₀ x y)

  trans-≺₁ x         (wkn (α≺s y))   = α≺s (wkn (trans-≺₁ x y))
  trans-≺₁ x         (wkn (α≺l n y)) = α≺l n (wkn (trans-≺₁ x y))
  trans-≺₁ x         (wkn (α≺⊔₀ y))  = α≺⊔₀ (trans-≺₁ x (wkn y))
  trans-≺₁ x         (wkn (α≺⊔₁ y))  = α≺⊔₁ (trans-≺₁ x (wkn y))
  trans-≺₁ (α≺s x)   (s≼α y)         = trans-≺₀ x y
  trans-≺₁ (α≺l n x) (l≼α {u = u} y) = trans-≺₀ x (trans-≺₁ (u n) (y (su n)))
  trans-≺₁ (α≺⊔₀ x)  (⊔≼α y₀ y₁)     = trans-≺₁ x y₀
  trans-≺₁ (α≺⊔₁ x)  (⊔≼α y₀ y₁)     = trans-≺₁ x y₁

  norm-s : ∀ {α β} → su α ≼ β → α ≺ β
  norm-s (s≼α x)         = x
  norm-s (wkn (α≺s x))   = α≺s (wkn (norm-s x))
  norm-s (wkn (α≺l n x)) = α≺l n (wkn (norm-s x))
  norm-s (wkn (α≺⊔₀ x))  = α≺⊔₀ (norm-s (wkn x))
  norm-s (wkn (α≺⊔₁ x))  = α≺⊔₁ (norm-s (wkn x))

  norm'-s : ∀ {α β} → su α ≺ su β → α ≺ β
  norm'-s (α≺s (s≼α x))         = x
  norm'-s (α≺s (wkn (α≺s x)))   = α≺s (wkn (norm'-s (α≺s x)))
  norm'-s (α≺s (wkn (α≺l n x))) = α≺l n (wkn (norm'-s (α≺s x)))
  norm'-s (α≺s (wkn (α≺⊔₀ x)))  = α≺⊔₀ (norm'-s (α≺s (wkn x)))
  norm'-s (α≺s (wkn (α≺⊔₁ x)))  = α≺⊔₁ (norm'-s (α≺s (wkn x)))

  norm-⊔₀ : ∀ {α β γ} → α ⊔ β ≼ γ → α ≼ γ
  norm-⊔₀ (⊔≼α x y)       = x
  norm-⊔₀ (wkn (α≺s x))   = wkn (α≺s (norm-⊔₀ x))
  norm-⊔₀ (wkn (α≺l n x)) = wkn (α≺l n (norm-⊔₀ x))
  norm-⊔₀ (wkn (α≺⊔₀ x))  = α≼⊔₀ (norm-⊔₀ (wkn x))
  norm-⊔₀ (wkn (α≺⊔₁ x))  = α≼⊔₁ (norm-⊔₀ (wkn x))

  norm-⊔₁ : ∀ {α β γ} → α ⊔ β ≼ γ → β ≼ γ
  norm-⊔₁ (⊔≼α x y)       = y
  norm-⊔₁ (wkn (α≺s x))   = wkn (α≺s (norm-⊔₁ x))
  norm-⊔₁ (wkn (α≺l n x)) = wkn (α≺l n (norm-⊔₁ x))
  norm-⊔₁ (wkn (α≺⊔₀ x))  = α≼⊔₀ (norm-⊔₁ (wkn x))
  norm-⊔₁ (wkn (α≺⊔₁ x))  = α≼⊔₁ (norm-⊔₁ (wkn x))

  norm'-⊔₀ : ∀ {α β γ} → α ⊔ β ≺ γ → α ≺ γ
  norm'-⊔₀ (α≺s x)   = α≺s (norm-⊔₀ x)
  norm'-⊔₀ (α≺l n x) = α≺l n (norm-⊔₀ x)
  norm'-⊔₀ (α≺⊔₀ x)  = α≺⊔₀ (norm'-⊔₀ x)
  norm'-⊔₀ (α≺⊔₁ x)  = α≺⊔₁ (norm'-⊔₀ x)

  norm'-⊔₁ : ∀ {α β γ} → α ⊔ β ≺ γ → β ≺ γ
  norm'-⊔₁ (α≺s x)   = α≺s (norm-⊔₁ x)
  norm'-⊔₁ (α≺l n x) = α≺l n (norm-⊔₁ x)
  norm'-⊔₁ (α≺⊔₀ x)  = α≺⊔₀ (norm'-⊔₁ x)
  norm'-⊔₁ (α≺⊔₁ x)  = α≺⊔₁ (norm'-⊔₁ x)

  norm-l : ∀ {φ u α} → li φ u ≼ α → (n : _) → φ n ≼ α
  norm-l (l≼α x)          n = x n
  norm-l (wkn (α≺s x))    n = wkn (α≺s (norm-l x n))
  norm-l (wkn (α≺l n₁ x)) n = wkn (α≺l n₁ (norm-l x n))
  norm-l (wkn (α≺⊔₀ x))   n = α≼⊔₀ (norm-l (wkn x) n)
  norm-l (wkn (α≺⊔₁ x))   n = α≼⊔₁ (norm-l (wkn x) n)

  --s-⊔ : ∀ {α β} → su (α ⊔ β) ≼ su α ⊔ su β
  --s-⊔ {α} {β} = s≼α {!  !}

  ⊔≺α : ∀ {α β γ} → α ≺ γ → β ≺ γ → α ⊔ β ≺ γ
  ⊔≺α (α≺s x) (α≺s y) = α≺s (⊔≼α x y)
  ⊔≺α (α≺l n x) (α≺l m y) = {!   !}
  ⊔≺α (α≺⊔₀ x) (α≺⊔₀ y) = α≺⊔₀ (⊔≺α x y)
  ⊔≺α (α≺⊔₀ x) (α≺⊔₁ y) = {!   !}
  ⊔≺α (α≺⊔₁ x) (α≺⊔₀ y) = {!   !}
  ⊔≺α (α≺⊔₁ x) (α≺⊔₁ y) = α≺⊔₁ (⊔≺α x y)

  irr : ∀ {α} → ¬ (α ≺ α)
  irr (α≺s x)           = irr (norm-s x)
  irr (α≺l {u = u} n x) = irr (trans-≺₁ (u n) (norm-l x (su n)))
  irr (α≺⊔₀ x)          = irr (norm'-⊔₀ x)
  irr (α≺⊔₁ x)          = irr (norm'-⊔₁ x)

  lem₀ : ∀ {α β} → α ≼ β → ¬ (β ≺ α)
  lem₀ x y = irr (trans-≺₀ x y)

  lem₁ : ∀ {α β} → α ≺ β → ¬ (β ≼ α)
  lem₁ x y = irr (trans-≺₁ x y)

  lem₂ : ∀ {α β} → α ≼ β → (β ≼ α) ∨ (α ≺ β)
  lem₂ {β = ze} z≼α = inl z≼α
  lem₂ {β = su β} z≼α = inr (α≺s z≼α)
  lem₂ {β = li φ u} z≼α = inr (α≺l ze z≼α)
  lem₂ {β = β₀ ⊔ β₁} z≼α with lem₂ {β = β₀} z≼α | lem₂ {β = β₁} z≼α
  ...                    | inl x | inl y = inl (⊔≼α x y)
  ...                    | inl x | inr y = inr (α≺⊔₁ y)
  ...                    | inr x | _     = inr (α≺⊔₀ x)
  lem₂ {β = ze} (s≼α x) = inl z≼α
  lem₂ {β = su β} (s≼α x) = {!   !}
  lem₂ {β = li φ u} (s≼α x) = {!   !}
  lem₂ {β = β ⊔ β₁} (s≼α x) = {!   !}
  lem₂ (l≼α x) = {!   !}
  lem₂ (⊔≼α x y) with lem₂ x | lem₂ y
  lem₂ (⊔≼α x y) | inl a | _     = inl (α≼⊔₀ a)
  lem₂ (⊔≼α x y) | inr a | inl b = inl (α≼⊔₁ b)
  lem₂ (⊔≼α x y) | inr a | inr b = inr {! ⊔≺α  !}
  lem₂ (wkn x) = {!   !}


open props


incr : (ord → ord) → Set
incr f = ∀ {α β} → α ≼ β → f α ≼ f β

s-incr : (ord → ord) → Set
s-incr f = ∀ {α β} → α ≺ β → f α ≺ f β

foo : ∀ {f} → s-incr f → incr f
foo p x = {!   !}

module arith where

  _+_ : ord → ord → ord
  +-incr : ∀ {α} → incr (_+_ α)
  +-sincr : ∀ {α} → s-incr (_+_ α)

  α + ze        = α
  α + su β      = su (α + β)
  α + li φ u    = li (λ n → α + φ n) (λ n → +-sincr (u n))
  α + (β₀ ⊔ β₁) = (α + β₀) ⊔ (α + β₁)

  +-incr z≼α = {!   !}
  +-incr (s≼α x) = s≼α (+-sincr x)
  +-incr (l≼α x) = l≼α (λ n → +-incr (x n))
  +-incr (⊔≼α x₀ x₁) = ⊔≼α (+-incr x₀) (+-incr x₁)
  +-incr (wkn x) = wkn (+-sincr x)

  +-sincr (α≺s x) = α≺s (+-incr x)
  +-sincr (α≺l n x) = α≺l n (+-incr x)
  +-sincr (α≺⊔₀ x) = α≺⊔₀ (+-sincr x)
  +-sincr (α≺⊔₁ x) = α≺⊔₁ (+-sincr x)


module utils where

  elim : (x : ord) (f : ord → ord) (p : (α : _) → α ≺ f α) → ord → ord
  elim-incr : ∀ {x f p α β} → α ≺ β → elim x f p α ≺ elim x f p β
  elim-incr' : ∀ {x f p α β} → α ≼ β → elim x f p α ≼ elim x f p β

  elim x f p ze       = x
  elim x f p (su α)   = f (elim x f p α)
  elim x f p (li φ u) = li (λ n → elim x f p (φ n)) (λ n → elim-incr (u n))
  elim x f p (α ⊔ β)  = (elim x f p α) ⊔ (elim x f p β)

  elim-incr {p = p} (α≺s x) = trans-≺₀ (elim-incr' x) (p _)
  elim-incr (α≺l n x) = α≺l n (elim-incr' x)
  elim-incr (α≺⊔₀ x) = α≺⊔₀ (elim-incr x)
  elim-incr (α≺⊔₁ x) = α≺⊔₁ (elim-incr x)

  elim-incr' z≼α = {!   !}
  elim-incr' {p = p} (s≼α x) = {! trans-≺₀ ? (elim-incr x)  !}
  elim-incr' (l≼α x) = l≼α (λ n → elim-incr' (x n))
  elim-incr' (⊔≼α x₀ x₁) = ⊔≼α (elim-incr' x₀) (elim-incr' x₁)
  elim-incr' (wkn x) = wkn (elim-incr x)


{-inj : nat → ord
inj ze     = ze
inj (su n) = su (inj n)

ω : ord
ω = li inj λ _ → α≺s refl

record normal (f : ord → ord) : Set where
  field
    mono : ∀ {α β} → α ≺ β → f α ≺ f β
    cont : ∀ {φ u} → f (li φ u) ≃ li (λ n → f (φ n)) λ n → mono (u n)
open normal public

lem : ∀ {f α} → normal f → α ≼ f α
lem {f} {ze} x = z≼α
lem {f} {su α} x = s≼α (trans-≺₀ (lem x) (mono x (α≺s refl)))
lem {f} {li φ u} x = l≼α (λ n → trans (wkn (α≺l n (lem x))) (β≼α (cont x)))

lem' : ∀ {f α} → normal f → ze ≺ f ze → α ≺ f α
lem' {f} {ze} x p = p
lem' {f} {su α} x p = trans-≺₀ (s≼α (lem' x p)) (mono x (α≺s refl))
lem' {f} {li φ u} x p = trans-≺₁ {! wkn  !} (β≼α (cont x))

δ : (f : ord → ord) (x : (α : ord) → α ≺ f α) → ord → ord
δ-mono : ∀ {f x α β} → α ≺ β → δ f x α ≺ δ f x β
--δ-fix : ∀ {f x α} → 

δ f x ze = li (elim-nat ze f) λ n → x _
δ f x (su α) = li (elim-nat (su (δ f x α)) f) λ n → x _
δ f x (li φ u) = li (λ n → δ f x (φ n)) λ n → δ-mono (u n)

δ-mono x₁ = {!   !}-}


--mono (elim-norm {α₀} {f} {u}) x = {! mono elim-norm x  !}
--cont elim-norm = {!   !}

{-fix : (f : ord → ord) (p : (α : ord) → α ≺ f α) → ord → ord
fix-≺ : ∀ {f p α β} → α ≺ β → fix f p α ≺ fix f p β

fix f p ze       = li (iter ze f) λ n → p _
fix f p (su α)   = li (iter (fix f p α) f) λ n → p _
fix f p (li φ x) = li (λ n → fix f p (φ n)) (λ n → fix-≺ (x n))

fix-≺ su-≺ = li-≺ ze
fix-≺ (li-≺ n) = li-≺ n
fix-≺ (trans-≺ x y) = trans-≺ (fix-≺ x) (fix-≺ y)

elim : (α₀ : ord) (f : ord → ord) (u : (α : ord) → α ≺ f α) → ord → ord
elim-fix : ∀ {α₀ f u α} → elim α₀ f u α ≃ f (elim α₀ f u α)
elim-mono : ∀ {α₀ f u α β} → α ≺ β → elim α₀ f u α ≺ elim α₀ f u β

elim α₀ f u ze       = li (elim-nat α₀ f) (λ n → u _)
elim α₀ f u (su α)   = li (elim-nat (elim α₀ f u α) f) (λ n → u _)
elim α₀ f u (li φ v) = li (λ n → elim α₀ f u (φ n)) λ n → elim-mono (v n)

α≼β (elim-fix {u = u}) = wkn (u _)
β≼α (elim-fix {α = ze}) = {!   !}
β≼α (elim-fix {α = su α}) = {!   !}
β≼α (elim-fix {α = li φ u}) = {!   !}

elim-mono (α≺s z≼α) = α≺l ze refl
elim-mono (α≺s (s≼α x)) = α≺l ze (l≼α {!   !})
elim-mono (α≺s (l≼α x)) = {!   !}
elim-mono (α≺s (wkn x)) = α≺l ze (wkn (elim-mono x))
elim-mono (α≺l n x) = ?
-}


{-_+_ : ord → ord → ord
+-mono : ∀ {α β γ} → β ≺ γ → α + β ≺ α + γ

α + ze = α
α + su β = su (α + β)
α + li f p = li (λ n → α + f n) (λ n → +-mono (p n))

+-mono su-≺ = su-≺
+-mono li-≺ = li-≺
+-mono (trans-≺ p q) = trans-≺ (+-mono p) (+-mono q)-}
