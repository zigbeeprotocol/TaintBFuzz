# Sandboxed Components

This directory is for Sandboxed components.
Sandboxed components are only visible in DEV mode (make dev).

The playground view « Sandbox » is also only visible in DEV mode and can be used to
play with sandboxed components _or_ any other component of the platform.

All files with `*.tsx` extension inside this directory will be automatically loaded
and shall register sandboxe(s) by using typically:

    Ivette.registerSandbox({
        id: 'sandbox.<ident>',
        label: 'My New Feature',
        title: 'Testing this new amazing feature',
        chidren: <MyNewFeature />,
    })

Enjoy Sandboxing !
