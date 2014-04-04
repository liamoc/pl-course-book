module ChapterOnePreliminaries where

module Equality where

  -- This essentially is a stripped down version of that equality relation, with
  -- only the necessary theorems included for convenience.

  infix 4 _≡_ 
  data _≡_ {A : Set} (x : A) : A → Set where
    refl : x ≡ x

  -- Cong allows us to apply a function to both sides of the equality.
  -- For example, if we have a proof that x = y, then we can apply cong
  -- suc to it to prove suc x = suc y.

  cong : {A : Set} {B : Set} (f : A → B) → ∀ {x y} → x ≡ y → f x ≡ f y
  cong f refl = refl

  -- Subst allows us to make use of equalities in a certain context. If
  -- Two different terms x and y are said to be equal, subst will provide
  -- the term in a y-formed type given a term in x-formed type.

  subst : ∀ {A : Set} → (P : A → Set) {x y : A} → x ≡ y → P x → P y
  subst P refl p = p

module Logic where

  -- An encoding of a disjunction (boolean OR) in Agda.
  -- We prove the disjunction by construction: If we can construct either
  -- an A or B in order to pass it to inl or inr respectively, we have
  -- proven that either A or B is constructively true and therefore
  -- proven A ∨ B.

  data _∨_ (A : Set) (B : Set) : Set where
    inl : A → A ∨ B
    inr : B → A ∨ B

  -- Implication is merely a function arrow in Agda, so we model it as such.

  _⇒_ : Set → Set → Set
  a ⇒ b = a → b

  -- Conjunction is equivalent to a pair or product, just as disjunction is an
  -- Either type or sum. 

  data _∧_ (A : Set) (B : Set) : Set where
    _,_ : A → B → A ∧ B

  -- Bijection a.k.a logical equivalence is just implication and reverse implication.

  _⇔_ : Set → Set → Set
  a ⇔ b = (a ⇒ b) ∧ (b ⇒ a)

module Strings where
  open Equality

  -- We only have two symbols in our string model, but adding any additional symbols would
  -- not affect the proof. Σ stands for the alphabet of possible symbols.

  data Σ : Set where
    `⟨` : Σ
    `⟩` : Σ

  -- String is simly a list type of Σ symbols, with the empty list represented as ε.

  data String : Set where
    ε : String
    _∷_ : Σ → String → String

  -- String concatenation or juxtaposition is represented with the ○ operator.

  infixl 6 _○_
  _○_ : String → String → String
  ε ○ a = a
  (x ∷ xs) ○ a = x ∷ (xs ○ a)
  
  -- Identity with ε:

  ○-id : ∀ {s : String} → s ○ ε ≡ s 
  ○-id {ε} = refl
  ○-id {x ∷ xs} = cong (_∷_ x) (○-id {xs})

  -- Associativity of ○:

  ○-assoc : ∀ {a b c : String} → a ○ (b ○ c) ≡ (a ○ b) ○ c
  ○-assoc {ε} = refl
  ○-assoc {x ∷ xs} = cong (_∷_ x) (○-assoc {xs}) 


  -- Pretty shortcut to make things look better and clearer
  -- Wraps a string in brackets.

  ⟨_⟩ : String → String
  ⟨ x ⟩ = `⟨` ∷ (x ○ (`⟩` ∷ ε))

module Preliminaries where

open Strings
open Equality
open Logic

-- Languages are encoded as data types.
-- We can only construct terms in the language if they conform to the rules.

data _M : String → Set where
  ε-rule : ε M                                     -- epsilon is in M
  ⟨⟩-rule : ∀ {a} → a M ⇒ ⟨ a ⟩ M                  -- for any string a in M, ⟨ a ⟩ is in M.
  juxtaposition : ∀ {a b} → a M → b M ⇒ (a ○ b) M -- for any two strings in M a and b, ab is in M.


data ⊥ : Set where -- nothing

-- L and N are mutually recursive - they refer to each other recursively, so 
-- we use a mutual block. Without it, Agda couldn't see N in the definition of L,
-- or if we swapped them around, it would then not see L in the definition of N.

mutual 
  data _L : String → Set where
    ε-rule′ : ε L                                             -- epsilon is always in L
    juxtaposition′ : {a b : String} → a N → b L ⇒ (a ○ b) L   -- if a in N and b in L, ab is in L

  data _N : String → Set where
    ⟨⟩-rule′ : ∀ {a} → a L ⇒ ⟨ a ⟩ N                           -- if a in L, ⟨ a ⟩ in N.

-- We now prove these languages equivalent.

-- First, we show that any string in M is in L.

proof-M→L : ∀ {s : String} → s M → s L
proof-M→L ε-rule = ε-rule′                            -- for the string ε, it is axiomatically in both M and L.

proof-M→L (⟨⟩-rule aM) = N→L (⟨⟩-rule′ (proof-M→L aM)) 
      -- for some string ⟨ a ⟩ where a is in M, we use the induction hypothesis to
      -- show that a is in L, then simply use the ⟨⟩-rule of the N language to show 
      -- ⟨ a ⟩ in N, then show (below) that any s in N is in L as required.
   where     
     N→L : ∀ {s : String} → s N → s L  -- Proof that all s in N are also in L
     N→L {s} sN = subst _L ○-id (juxtaposition′ sN ε-rule′) 
       -- The trick here is that any s in N can be juxtaposed with ε, which we know from
       -- the identity rule for ○. s ○ ε is in L from L's juxtaposition rule.

proof-M→L (juxtaposition aM bM) = lemma (proof-M→L aM) (proof-M→L bM)
       -- Here we just turn the crank and use the induction hypothesis twice to show that
       -- both juxtaposed substrings a and b (in M) are in L, and then show that the
       -- juxtaposition of two substrings in L is also in L (below)
   where
     lemma : ∀ {a b : String} → a L → b L → (a ○ b) L -- Proof that two strings in L are in L when concatenated.
     lemma (ε-rule′) bL = bL 
        --  When a is empty, the string is simply b.
        --  ε ○ b = b by definition, so no substitution is required.
     lemma {b = b} (juxtaposition′ {a₁} {a₂} a₁N a₂L) bL = subst _L (○-assoc {a₁} {a₂} {b}) 
                                                                    (juxtaposition′ a₁N (lemma a₂L bL))    
        -- When we have a juxtaposition of two substrings in the first string, our proof goal becomes:
        -- a₁a₂b L, where a₁N, a₂L, b L
        -- We use the induction hypothesis on a₂ and b, producing judgement a₂b L.
        -- We then use the juxtaposition rule of L to prepend a₁, giving a₁a₂b L. 
        -- Agda does not immediately understand associativity of concatenation, so we need to do a bit
        -- of equality substitution.

-- Now we prove in the other direction, a substantially simpler proof, however we use simultaneous induction rather
-- than simple structural induction.

mutual 
  proof-L→M : ∀ {s : String} → s L → s M
  proof-L→M (ε-rule′) = ε-rule -- ε always is easy.
  proof-L→M (juxtaposition′ {s₁} {s₂} s₁N s₂L)  = juxtaposition (proof-N→M {s₁} s₁N) (proof-L→M {s₂} s₂L)
  -- For a juxtaposition of two strings s₁ and s₂, s₁ is in N and s₂ is in L. We use the simultaneous 
  -- inductive hypothesis (from the proof below) to show s₁ in M from s₁ in N, and use the standard structural 
  -- induction to show s₂ in M from s₂ in L.
  proof-N→M : ∀ {s : String} → s N → s M 
  proof-N→M (⟨⟩-rule′ aL) = ⟨⟩-rule (proof-L→M aL)
--Now we combine the two to show N and M equivalent.
proof : ∀ {s : String} → s M ⇔ s L
proof = (proof-M→L , proof-L→M)
