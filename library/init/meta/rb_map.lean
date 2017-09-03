/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
prelude
import init.data.ordering init.function init.meta.name init.meta.format init.category.monad

meta constant {u₁ u₂} rb_map : Type u₁ → Type u₂ → Type (max u₁ u₂)

namespace rb_map
meta constant mk_core {key : Type} (data : Type)        : (key → key → ordering) → rb_map key data
meta constant size {key : Type} {data : Type}           : rb_map key data → nat
meta constant empty {key : Type} {data : Type}          : rb_map key data → bool
meta constant insert {key : Type} {data : Type}         : rb_map key data → key → data → rb_map key data
meta constant erase  {key : Type} {data : Type}         : rb_map key data → key → rb_map key data
meta constant contains {key : Type} {data : Type}       : rb_map key data → key → bool
meta constant find {key : Type} {data : Type}           : rb_map key data → key → option data
meta constant min {key : Type} {data : Type}            : rb_map key data → option data
meta constant max {key : Type} {data : Type}            : rb_map key data → option data
meta constant fold {key : Type} {data : Type} {α :Type} : rb_map key data → α → (key → data → α → α) → α

attribute [inline]
meta def mk (key : Type) [has_ordering key] (data : Type) : rb_map key data :=
mk_core data has_ordering.cmp

open list
meta def of_list {key : Type} {data : Type} [has_ordering key] : list (key × data) → rb_map key data
| []           := mk key data
| ((k, v)::ls) := insert (of_list ls) k v

meta def keys {key : Type} {data : Type} (m : rb_map key data) : list key :=
fold m [] (λk v ks, k :: ks)

meta def values {key : Type} {data : Type} (m : rb_map key data) : list data :=
fold m [] (λk v vs, v :: vs)

meta def to_list {key : Type} {data : Type} (m : rb_map key data) : list (key × data) :=
fold m [] (λk v res, (k, v) :: res)

meta def set_of_list {A} [has_ordering A] : list A → rb_map A unit
| []      := mk _ _
| (x::xs) := insert (set_of_list xs) x ()

meta def map {A B C} [has_ordering A] (f : B → C) (m : rb_map A B) : rb_map A C :=
fold m (mk _ _) (λk v res, insert res k (f v))

meta def for {A B C} [has_ordering A] (m : rb_map A B) (f : B → C) : rb_map A C :=
map f m

meta def filter {A B} [has_ordering A] (m : rb_map A B) (f : B → Prop) [decidable_pred f] :=
fold m (mk _ _) $ λa b m', if f b then insert m' a b else m'

meta def mfold {key data α :Type} {m : Type → Type} [monad m] (mp : rb_map key data) (a : α) (fn : key → data → α → m α) : m α :=
mp.fold (return a) (λ k d act, act >>= fn k d)

end rb_map

meta def mk_rb_map {key data : Type} [has_ordering key] : rb_map key data :=
rb_map.mk key data

@[reducible] meta def nat_map (data : Type) := rb_map nat data
namespace nat_map
export rb_map (hiding mk)

meta def mk (data : Type) : nat_map data := rb_map.mk nat data
end nat_map

meta def mk_nat_map {data : Type} : nat_map data :=
nat_map.mk data

@[reducible] meta def name_map (data : Type) := rb_map name data
namespace name_map
export rb_map (hiding mk)

meta def mk (data : Type) : name_map data := rb_map.mk name data
end name_map

meta def mk_name_map {data : Type} : name_map data :=
name_map.mk data

open rb_map prod
section
open formattable
variables {γ : Type} [formattable γ]
variables {key : Type} {data : Type} [has_to_fmt γ key] [has_to_fmt γ data]
private meta def format_key_data (k : key) (d : data) (first : bool) : γ :=
(if first then ↑"" else ↑"," ++ line) ++ to_fmt k ++ ↑" ← " ++ to_fmt d

meta instance : has_to_fmt γ (rb_map key data) :=
⟨λ m, group $ ↑"⟨" ++ nest 1 (fst (fold m ((↑"" : γ), tt) (λ k d p, (fst p ++ format_key_data k d (snd p), ff)))) ++
              ↑"⟩"⟩
end

/-- a variant of rb_maps that stores a list of elements for each key.
   `find` returns the list of elements in the opposite order that they were inserted. -/
meta def rb_lmap (key : Type) (data : Type) : Type := rb_map key (list data)

namespace rb_lmap

protected meta def mk (key : Type) [has_ordering key] (data : Type) : rb_lmap key data :=
rb_map.mk key (list data)

meta def insert {key : Type} {data : Type} (rbl : rb_lmap key data) (k : key) (d : data) :
  rb_lmap key data :=
match (rb_map.find rbl k) with
| none     := rb_map.insert rbl k [d]
| (some l) := rb_map.insert (rb_map.erase rbl k) k (d :: l)
end

meta def erase {key : Type} {data : Type} (rbl : rb_lmap key data) (k : key) :
  rb_lmap key data :=
rb_map.erase rbl k

meta def contains {key : Type} {data : Type} (rbl : rb_lmap key data) (k : key) : bool :=
rb_map.contains rbl k

meta def find {key : Type} {data : Type} (rbl : rb_lmap key data) (k : key) : list data :=
match (rb_map.find rbl k) with
| none     := []
| (some l) := l
end

end rb_lmap

meta def rb_set (key) := rb_map key unit
meta def mk_rb_set {key} [has_ordering key] : rb_set key :=
mk_rb_map

variables {γ : Type} [formattable γ]
open formattable

private meta def format_key {key} [has_to_fmt γ key] (k : key) (first : bool) : γ :=
(if first then ↑"" else ↑"," ++ line) ++ to_fmt k

namespace rb_set
meta def insert {key} (s : rb_set key) (k : key) : rb_set key :=
rb_map.insert s k ()

meta def erase {key} (s : rb_set key) (k : key) : rb_set key :=
rb_map.erase s k

meta def contains {key} (s : rb_set key) (k : key) : bool :=
rb_map.contains s k

meta def size {key} (s : rb_set key) : nat :=
rb_map.size s

meta def empty {key : Type} (s : rb_set key) : bool :=
rb_map.empty s

meta def fold {key α : Type} (s : rb_set key) (a : α) (fn : key → α → α) : α :=
rb_map.fold s a (λ k _ a, fn k a)

meta def mfold {key α :Type} {m : Type → Type} [monad m] (s : rb_set key) (a : α) (fn : key → α → m α) : m α :=
s.fold (return a) (λ k act, act >>= fn k)

meta def to_list {key : Type} (s : rb_set key) : list key :=
s.fold [] list.cons

meta instance {key} [has_to_fmt γ key] : has_to_fmt γ (rb_set key) :=
⟨λ m, group $ ↑"{" ++ nest 1 (fst (fold m ((↑"" : γ), tt) (λ k p, (fst p ++ format_key k (snd p), ff)))) ++
              ↑"}"⟩
end rb_set

meta constant name_set : Type
meta constant mk_name_set : name_set

namespace name_set
meta constant insert         : name_set → name → name_set
meta constant erase          : name_set → name → name_set
meta constant contains       : name_set → name → bool
meta constant size           : name_set → nat
meta constant empty          : name_set → bool
meta constant fold {α :Type} : name_set → α → (name → α → α) → α

meta def to_list (s : name_set) : list name :=
s.fold [] list.cons

meta instance : has_to_fmt γ name_set :=
⟨λ m, group $ ↑"{" ++ nest 1 (fst (fold m ((↑"" : γ), tt) (λ k p, (fst p ++ format_key k (snd p), ff)))) ++
              ↑"}"⟩

meta def of_list (l : list name) : name_set :=
list.foldl name_set.insert mk_name_set l

meta def mfold {α :Type} {m : Type → Type} [monad m] (ns : name_set) (a : α) (fn : name → α → m α) : m α :=
ns.fold (return a) (λ k act, act >>= fn k)

end name_set
