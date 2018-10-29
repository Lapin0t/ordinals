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

data ord : Set
data _≼_ : ord → ord → Set
data _≺_ : ord → ord → Set

data ord where
  ze : ord
  su : ord → ord
  li : (φ : nat → ord) (u : (n : nat) → φ n ≺ φ (su n)) → ord

data _≼_ where
  z≼z : ze ≼ ze
  s≼α : ∀ {α β} → α ≺ β → su α ≼ β
  l≼α : ∀ {φ u α} → ((n : nat) → φ n ≼ α) → li φ u ≼ α
  wkn : ∀ {α β} → α ≺ β → α ≼ β

data _≺_ where
  α≺s : ∀ {α β} → α ≼ β → α ≺ su β
  α≺l : ∀ {φ u α} (n : nat) → α ≼ φ n → α ≺ li φ u

record _≃_ (α β : ord) : Set where
  field
    α≼β : α ≼ β
    β≼α : β ≼ α
open _≃_ public


--- Constructors alternate forms

z≼α : ∀ {α} → ze ≼ α
z≼α {ze} = z≼z
z≼α {su α} = wkn (α≺s z≼α)
z≼α {li φ u} = wkn (α≺l ze z≼α)

s≼s : ∀ {α β} → α ≼ β → su α ≼ su β
s≼s x = s≼α (α≺s x)

s≺s : ∀ {α β} → α ≺ β → su α ≺ su β
s≺s x = α≺s (s≼α x)


module props where

  refl : ∀ {α} → α ≼ α
  refl {ze}     = z≼z
  refl {su _}   = s≼s refl
  refl {li _ _} = l≼α (λ n → wkn (α≺l n refl))

  trans : ∀ {α β γ} → α ≼ β → β ≼ γ → α ≼ γ
  trans-≺₀ : ∀ {α β γ} → α ≼ β → β ≺ γ → α ≺ γ
  trans-≺₁ : ∀ {α β γ} → α ≺ β → β ≼ γ → α ≺ γ

  trans z≼z       y       = y
  trans (wkn x)   y       = wkn (trans-≺₁ x y)
  trans x         (wkn y) = wkn (trans-≺₀ x y)
  trans (l≼α x)   y       = l≼α (λ n → trans (x n) y)
  trans (s≼α x)   y       = s≼α (trans-≺₁ x y)

  trans-≺₀ x (α≺s y)   = α≺s (trans x y)
  trans-≺₀ x (α≺l n y) = α≺l n (trans x y)

  trans-≺₁ x         (wkn (α≺s y))   = α≺s (wkn (trans-≺₁ x y))
  trans-≺₁ x         (wkn (α≺l n y)) = α≺l n (wkn (trans-≺₁ x y))
  trans-≺₁ (α≺s x)   (s≼α y)         = trans-≺₀ x y
  trans-≺₁ (α≺l n x) (l≼α {u = u} y) = trans-≺₀ x (trans-≺₁ (u n) (y (su n)))

  norm-s : ∀ {α β} → su α ≼ β → α ≺ β
  norm-s (s≼α x)         = x
  norm-s (wkn (α≺s x))   = α≺s (wkn (norm-s x))
  norm-s (wkn (α≺l n x)) = α≺l n (wkn (norm-s x))

  norm'-s : ∀ {α β} → su α ≺ su β → α ≺ β
  norm'-s (α≺s (s≼α x))         = x
  norm'-s (α≺s (wkn (α≺s x)))   = α≺s (wkn (norm'-s (α≺s x)))
  norm'-s (α≺s (wkn (α≺l n x))) = α≺l n (wkn (norm'-s (α≺s x)))

  norm-l : ∀ {φ u α} → li φ u ≼ α → (n : _) → φ n ≼ α
  norm-l (l≼α x)          n = x n
  norm-l (wkn (α≺s x))    n = wkn (α≺s (norm-l x n))
  norm-l (wkn (α≺l n₁ x)) n = wkn (α≺l n₁ (norm-l x n))

  irr : ∀ {α} → ¬ (α ≺ α)
  irr (α≺s x)           = irr (norm-s x)
  irr (α≺l {u = u} n x) = irr (trans-≺₁ (u n) (norm-l x (su n)))

  lem₀ : ∀ {α β} → α ≼ β → ¬ (β ≺ α)
  lem₀ x y = irr (trans-≺₀ x y)

  lem₁ : ∀ {α β} → α ≺ β → ¬ (β ≼ α)
  lem₁ x y = irr (trans-≺₁ x y)


open props


incr : (ord → ord) → Set
incr f = ∀ {α β} → α ≼ β → f α ≼ f β

s-incr : (ord → ord) → Set
s-incr f = ∀ {α β} → α ≺ β → f α ≺ f β

foo : ∀ {f} → s-incr f → incr f
foo p x = {!   !}

{-module arith where

  _+_ : ord → ord → ord
  +-incr : ∀ {α} → incr (_+_ α)
  +-sincr : ∀ {α} → s-incr (_+_ α)

  α + ze        = α
  α + su β      = su (α + β)
  α + li φ u    = li (λ n → α + φ n) (λ n → +-sincr (u n))

  +-incr z≼z = {!   !}
  +-incr (s≼α x) = s≼α (+-sincr x)
  +-incr (l≼α x) = l≼α (λ n → +-incr (x n))
  +-incr (wkn x) = wkn (+-sincr x)

  +-sincr (α≺s x) = α≺s (+-incr x)
  +-sincr (α≺l n x) = α≺l n (+-incr x)-}

module utils where
  record normal (f : ord → ord) : Set where
    field
      mono : ∀ {α β} → α ≺ β → f α ≺ f β
      cont : ∀ {φ u} → f (li φ u) ≃ li (λ n → f (φ n)) λ n → mono (u n)
  open normal public

  lem : ∀ {f α} → normal f → α ≼ f α
  lem {f} {ze} x = z≼α
  lem {f} {su α} x = s≼α (trans-≺₀ (lem x) (mono x (α≺s refl)))
  lem {f} {li φ u} x = l≼α (λ n → trans (wkn (α≺l n (lem x))) (β≼α (cont x)))

  lem' : (f : ord → ord) (p : normal f) → ∀ {α β} → α ≼ β → f α ≼ f β
  lem' f p {.ze} {.ze} z≼z = refl
  lem' f p {.(su _)} {.(su _)} (s≼α (α≺s x)) = {! (mono p (α≺s refl))!}
  lem' f p {.(su _)} {.(li _ _)} (s≼α (α≺l {u = u} n x)) = trans (wkn (α≺l (su n) (lem' f p (trans (s≼s x) (s≼α (u n)))))) (β≼α (cont p))
  lem' f p {.(li _ _)} {β} (l≼α x) = trans (α≼β (cont p)) (l≼α (λ n → lem' f p (x n)))
  lem' f p {α} {β} (wkn x) = wkn (mono p x)

  fix : (f : ord → ord) (p : (α : _) → α ≺ f α) → ord → ord
  fix-incr : ∀ {f p α β} → α ≺ β → fix f p α ≺ fix f p β
  fix-incr' : ∀ {f p α β} → α ≼ β → fix f p α ≼ fix f p β
  fix-fix : ∀ {f p} (α : ord) → f (fix f p α) ≼ fix f p α

  fix f p ze       = li (elim-nat ze f) (λ n → p (elim-nat ze f n))
  fix f p (su α)   = li (elim-nat (su (fix f p α)) f) (λ n → p (elim-nat (su (fix f p α)) f n))
  fix f p (li φ u) = li (λ n → fix f p (φ n)) (λ n → fix-incr (u n))

  fix-incr {p = p} (α≺s x) = α≺l ze (wkn (α≺s (fix-incr' x)))
  fix-incr (α≺l n x) = α≺l n (fix-incr' x)

  fix-fix ze = {!   !}
  fix-fix (su α) = {!   !}
  fix-fix (li φ u) = {!   !}

  fix-incr' {β = ze} z≼z = refl
  fix-incr' {f} {p} {su α} {su β} (s≼α (α≺s x)) = {!   !}
    where
      aux : (n : nat) → elim-nat (fix f p α) f n ≼ elim-nat (fix f p β) f n
      aux ze = fix-incr' x
      aux (su n) = {!  aux n !}
  fix-incr' {f} {p} {su α} {.(li _ _)} (s≼α (α≺l n x)) = {!   !}
  --fix-incr' {f} {p} {su α} {li φ u} (s≼α (α≺l n x)) = {!   !}
    {-where
      aux ze = l≼α (λ n → {!   !})
      aux (su n) = {!   !}-}
  fix-incr' (l≼α x) = l≼α (λ n → fix-incr' (x n))
  fix-incr' (wkn x) = wkn (fix-incr x)


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
