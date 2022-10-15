---
subtitle: Custom React Hooks
---

The **Dome** framework provides several [React Hooks](https://reactjs.org/docs/hooks-intro.html)
to ease your developpement process. Here is a summary of them.

- [`useUpdate(evt)`](dome_.html#.useUpdate) to trigger re-rendering on **Dome** events;
- [`useEvent(emitter,event,callback)`](dome_.html#.useEvent) to trigger callbacks on events;
- [`useForceUpdate()`](dome_.html#.useForceUpdate) to trigger re-rendering on demand;
- [`useState(settings,defaultValue)`](dome_.html#.useState)
  similar to `React.useState()` with optional persistent _window_ settings;
- [`useSwitch(settings,defaultValue)`](dome_.html#.useSwitch)
  similar to `React.useState()` for boolean values with _window_ settings;
- [`useGlobalSetting(settings,defaultValue)`](dome_.html#.useGlobalSetting)
  similar to `React.useState()` with optional persistent _global_ settings;
- [`useHistory(settings,defaultValue)`](dome_.html#.useHistory)
  for managing histories
- [`useClock(period,initStart)`](dome_.html#.useClock)
returns start/stop clocks synchronized on period.
- [`useCommand()`](dome_.html#.useCommand) for working with different application instances.
- See also the [`Dome.State`](dome(renderer).State.html) and the associated hooks.
