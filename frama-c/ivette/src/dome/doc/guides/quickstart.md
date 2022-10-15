---
subtitle: Quick Start
---

We strongly recommand to use [**Yarn**](https://reactjs.org)
for installing the necessary Node packages and their dependencies.

Then, prepare a directory for developing your application, and download
the Dome Application Framework into sub-directory `dome`.
You shall now setup a makefile for your application as follows:

<pre>
  # Makefile
  include dome/template/makefile
  all: dome-dev
</pre>

Now, simply type `make` and all the necessary packages will be automatically
installed and configured. This can take a while for the very first installation.
You will be prompted for generating a default `package.json` file
if you do not have some already.

Eventually, your application will start with
a « _Hello World_ » window.
Now, you can _live edit_ the generated `src/renderer/Application.js` which is the main entry point
of your application and see what happens into the main window.
