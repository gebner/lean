/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.options init.function init.data.to_string

universes u v

inductive format.color
| red | green | orange | blue | pink | cyan | grey

meta constant format : Type
meta constant format.line            : format
meta constant format.space           : format
meta constant format.nil             : format
meta constant format.compose         : format → format → format
meta constant format.nest            : nat → format → format
meta constant format.highlight       : format → color → format
meta constant format.group           : format → format
meta constant format.of_string       : string → format
meta constant format.of_nat          : nat → format
meta constant format.flatten         : format → format
meta constant format.to_string  (f : format) (o : options := options.mk) : string
meta constant format.of_options      : options → format
meta constant format.is_nil          : format → bool
meta constant trace_fmt {α : Type u} : format → (unit → α) → α

meta instance : formattable format :=
{ append := format.compose, line' := format.line,
  of_string' := format.of_string, of_nat' := format.of_nat,
  nest := format.nest, group := format.group }

@[priority 10]
meta instance (γ : Type u) [formattable γ] : has_to_fmt γ format :=
⟨λ f, to_fmt $ f.to_string options.mk⟩

meta instance : has_coe string format :=
⟨formattable.of_string⟩

open format list

meta def format.when {α : Type u} [has_to_fmt format α] : bool → α → format
| tt a := to_fmt a
| ff a := nil

meta instance : has_to_fmt format options :=
⟨λ o, format.of_options o⟩
