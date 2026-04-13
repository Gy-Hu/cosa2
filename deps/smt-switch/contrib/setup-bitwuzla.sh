#!/bin/bash
git_commit=4b4384fe43e03d0a941c6f5b1107fad86960b623

prepare_step() {
  "$contrib_dir/setup-cadical.sh"
}

configure_step() {
  ./configure.py --prefix "$install_dir"
}

# shellcheck source=contrib/meson-setup.sh
source "$(dirname "$(realpath "$0")")/meson-setup.sh"
