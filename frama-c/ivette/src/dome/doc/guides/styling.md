---
subtitle: Styling Components
---

This tutorial explains how **Dome** style sheets are organized and how
to reuse them for styling your own components. Although modern styling
usually rely on _style preprocessors_ to leverage the complexity of
CSS style sheets development, the approach used here is based on separation
of concerns and multi-class styling. The advantage is that you can
develop your _own_ style sheets, while still being able
to re-use the existing classes provided by the framework.

All CSS classes provided by **Dome** start with prefix `dome-` ; you shall not
use such a prefix when designing your own classes. Many class names are provided
with optional or mandatory variants. Typically:

- `dome-<base>[-<a>,<b>,...]` describes class `dome-<base>` and its variants
`dome-<base>-<a>`, `dome-<base>-<b>` _etc_.

- `dome-<name>-[<a>,<b>,...]` describes classes `dome-<name>-<a>`, `dome-<name>-<b>` _etc_.

## Platform Context

These classes can be used when writing selectors in order to style things
with respect to the target platform. The main window container is attributed
with one of the following class:

- `dome-platform-[darwin,linux,windows]` derived from the `process.darwin`
global variable (**Node.js** environment).

- `dome-window-[active|inactive]` depending on whether the main application window
has focus or not.

## Color Palettes

Attributing colors to graphical elements is often an issue, since a precise
hex variants shall be tuned depending on the surrounding context. However,
base colors are provided in public classes for several usages:

- `dome-color-frame` background, foreground and borders for
window frames, which includes tool-bars, status-bars, tabs and such.
Those colors actually depend on the focus state of the main application window.

- `dome-color-[dragzone|dragging]` for painting the background of a dragging
zone, typically a splitting rule. The `dragzone` variant is completely
transparent with a very transparent light gray when hovered.
The `dragging` variant is semi-transparent blended blue with light gray.
All these drag background effects are smoothly transitioned.

## Text Properties

- `dome-text-[label|title|descr]` for labels (_eg._ buttons, tabs, menu
entries), titles (larger labels) and descriptions (_eg._ tooltips).
Uses a sans-serif font, is non-selectable and truncated with an ellipsis.

- `dome-text-[data|code]` for selectable text, typically input fields.
Uses a sans-serif font (for `data`) or monospace font (for `code`),
never wraps and is clipped when overflow.

## Component Layout

The entire application uses the `box-model` box-sizing property by default,
since it is usually much more consistent with nested `<div>` components.
Similarly, default margins and paddings are set to `0px` to avoid unwanted
messy background issues.
