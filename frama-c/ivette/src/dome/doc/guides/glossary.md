---
subtitle: Glossary
---

## Basic Concepts

- **Component** a React Component definition (class of function)
- **Element** a React Component instance of a Component, typically `<Component ...>`
- **Elements** a fragment of any number of elements, typically the `children` properties of elements
- **Render Prop** a function returning element(s), typically used instead of children elements

## Component Properties

- `id` an element identifier
- `icon` an icon identifier, as listed in the [icon gallery](tutorial-icons.html)
- `label` a short text used as the displayed title of a component
- `text` textual content to be printed on screen
- `title` a description for a component, usually provided in a tooltip box
- `settings` a key for making local state(s) persistent in user's settings
- `value` the value associated to some basic control (see `onChange`)
- `state` an object holding some current state (see `onUpdate`)
- `default` identifies the element selected by default in a list
- `selected` whether an element is selected or not (never by default)
- `disabled` whether an element will not responds to user actions (never by default)
- `selection` the identifier or value of current selection, or `undefined` (see `onSelect`)
- `children` the children elements of a component instance
- `onClick` a callback function in response to a click event
- `onClose` a callback function in response to closing action
- `onChange` a callback function in response to value changes (see `value`)
- `onUpdate` a callback function in response to (partial) state updates (see `state`)
- `onSelection` a callback function in response to user selection (see `selection`)
- `style` an inlined CSS style object to inject in a DOM element
