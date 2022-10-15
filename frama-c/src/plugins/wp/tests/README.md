# Running qualif tests

- Be sure that you have installed the appropriate versions of
  alt-ergo and coq _before_ having compiled Frama-C.
- use `make wp-qualif` in the toplevel Frama-C directory

# Test Suites

Here is a short description of the WP test suites:

- `tests/wp` tests dedicated to the VC generation engine and proof strategy
- `tests/wp_tip` tests associated to the script engine
- `tests/wp_acsl` tests of generic C/ACSL concepts
- `tests/wp_typed` tests dedicated to aliasing memory model
- `tests/wp_hoare` tests dedicated to non-aliasing memory model
- `tests/wp_region` tests dedicated to region memory model
- `tests/wp_manual` tests for generating the examples of the reference manual
- `tests/wp_gallery` non-regression tests for representative real size usage of WP
- `tests/wp_plugin` general purpose WP plug-in options
- `tests/wp_bts` non-regression tests associated to GitLab issues; eg. `issue_xxx.i`

Deprecated test suites that shall be moved around:

- `tests/wp_usage` mostly movable to `tests/wp_plugin`
- `tests/wp_store` mostly movable to `tests/wp_typed`

# Test Configurations

There are two test configurations:
- the default one requires _no_ prover execution;
- the `qualif` configuration uses the `wp-cache` global cache, `Alt-Ergo` and `Coq`.

The test configurations `tests/test_config` and `tests/test_config_qualif` are
carefully crafted to fit with the constraints of the GitLab
Continuous Integration system. In particular, the `qualif` configuration is
designed for being used with a clone of the global WP cache, see
installation instructions below.

To re-run tests, use by default the following commands:
- `make Wp_TESTS` for the default test configuration;
- `make wp-qualif` for the `qualif` configuration.

When using the `wp-qualif` target, it will clone the global wp-cache at `../wp-cache` by default,
if not yet present. To choose another place, consult the « Global WP Cache »
installation instructions below.
The WP makefile provides several targets to automate cache management. It is highly
recommanded to use them most of the time:

- `make wp-qualif` re-runs qualif tests; no new cache entry is created, though.
- `make wp-qualif-env` prints the environment variables for wp-qualif.
- `make wp-qualif-update` re-runs and creates missing cache entries.
- `make wp-qualif-upgrade` creates missing cache entries _and_ updates test scripts if necessary.
- `make wp-qualif-push` commits and pushes all new cache entries to the GitLab repository.
- `make wp-qualif-status` displays a very short git status of your local wp-cache.

To execute a given test by hand in `qualif` configuration, use the following
commands in a _local_ shell:

    $ export FRAMAC_WP_CACHE=update
    $ export FRAMAC_WP_CACHEDIR=<path-to-wp-cache>
    $ ./bin/ptests.opt src/plugins/wp/tests/xxx/yyy.i -config qualif [-show|-update]

It is _highly_ recommanded to _not_ set the `FRAMAC_WP_xxx` variables globally;
doing so would causing WP to add new cache entries to the global « qualif » cache
from all your projects around. Consult the section « Global WP Cache Setup »
below for details.

Note that this cache is meant to be global, including for the different merge
requests. Thus, when working on a new merge request for WP, **do not** create a
branch (and MR) on the WP-cache repository: just push the new cache entries into
the global cache using `make wp-qualif-push`.

# Qualified Test Results

To be accepted by Frama-CI, tests in « qualif » configuration must be easily
reproducible on any platform. This is checked by running WP with flag
`-wp-msg-key shell` which is set by the default in the qualif test
configuration. Hence, a qualified test result only contains proof status that
are either:
- failed
- valid for qed or script
- cached for alt-ergo in all cases
- valid, unknown or stepout for native Alt-Ergo
- valid or unknown for (native) Coq

This excludes any timeout with native Alt-Ergo, which must be turned into some
reproducible stepout by setting `-wp-steps` and `-wp-timeout` options
accordingly. Please choose a step limit that makes large enough to ensure the
goal is provable, but small enough to make alt-ergo decide quickly.

# Global WP Cache Setup (for wp-qualif)

All prover results for test configuration `qualif` shall be cached in a dedicate
GitLab repo.  This considerally speed-up the process of running those tests,
from hours downto minutes.

To ease the management of cache entries accross merge requests,
_all_ cache entries shall be merged into the _same_ master branch of a global
repository, even if they come from _different_ Frama-C branches.
This strategy prevents merge conflicts related to different cache
entries and simplifies the review of MR, especially those modifying the VC
generation process. The gitLab Frama-CI continuous integration system is aware of
this strategy and always use the global cache.

By default, the WP makefile will clone a local copy of the wp-cache in `../wp-cache`
but you can choose another place with the following commands:

    $ git clone git@git.frama-c.com:frama-c/wp-cache.git <your-cache>
    $ export WP_QUALIF_CACHE=<absolute-path-to-your-cache>

The WP makefile uses `WP_QUALIF_CACHE` environment variable to know where your
local copy of cache has been installed. You shall put it in your global shell
environment. To run individual tests, you may now use:

    $ export FRAMAC_WP_CACHE=update
    $ export FRAMAC_WP_CACHEDIR=$WP_QUALIF_CACHE
    $ ./bin/ptests.opt src/plugins/wp/tests/xxx/yyy.i -config qualif [-show|-update]

An utility script is provided to export the necessary environment variables
(dont forget the `.` to execute the script in the current shell environment):

    $ . bin/wp_qualif.sh

As mentionned above, it is _not_ recommanded to globally set the
`FRAMAC_WP_XXX` variables in your default shell environment, because WP will
use it by default and would merge any new cache entry there, even those
non-related to the « qualif » test suite. For this reason,
it is _highly_ recommended to use `WP_QUALIF_CACHE` globally
and `FRAMAC_WP_CACHEDIR` locally.
