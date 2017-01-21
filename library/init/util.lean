/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.string.basic

/- This function has a native implementation that tracks time. -/
def timeit {α : Type} (s : string) (f : unit → α) : α :=
f ()

/- This function has a native implementation that displays the given string in the regular output stream. -/
def trace {α : Type} (s : string) (f : unit → α) : α :=
f ()

/- This function has a native implementation that shows the VM call stack. -/
def trace_call_stack {α : Type} (f : unit → α) : α :=
f ()

meta constant {u} undefined_core {α : Type u} (message : string) : α

meta def {u} undefined {α : Type u} : α := undefined_core "undefined"
