{-# OPTIONS --safe --without-K #-}

-- The shipped decks discharge `sane` by computation, so `render-fragments` and `ticks-fragments`
-- hold for them outright.  Each definition is a check: it stops typechecking if a class string of
-- the deck would put a fragment on the page that the model does not count.

module Slides.Backend.Render.Shipped where

open import Data.Bool.Base using (T)
open import Data.Unit.Base using (tt)

open import Slides.Backend.Render.Sane using (saneTalk)
import Slides.Examples.AnimRef as AnimRef
import Slides.Examples.Intro as Intro
import Slides.Examples.Labels as Labels
import Slides.Examples.Pairs as Pairs
import Slides.Examples.Plots as Plots
import Slides.Examples.Showcase as Showcase
import Slides.Examples.Talk as Talk
import Slides.Examples.Tensor as Tensor
import Slides.Examples.TextDemo as TextDemo

intro : T (saneTalk Intro.demo)
intro = tt

textDemo : T (saneTalk TextDemo.demo)
textDemo = tt

talk : T (saneTalk Talk.talk)
talk = tt

showcase : T (saneTalk Showcase.showcase)
showcase = tt

pairs : T (saneTalk Pairs.pairs)
pairs = tt

plots : T (saneTalk Plots.talk)
plots = tt

tensor : T (saneTalk Tensor.demo)
tensor = tt

labels : T (saneTalk Labels.labels)
labels = tt

animRef : T (saneTalk AnimRef.animations)
animRef = tt
