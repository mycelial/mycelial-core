## Python bindings to mycelial-crdt

## How to install:
* Install rust (https://rustup.rs/)  
* Install pyo3 build toolchain: `brew install maturin` or `cargo install maturin`  
* Install py virtualenv:  
  * `brew install virtualenvwrapper`
  * `echo ". virtualenvwrapper.sh" > ~/.bashrc`
  * `mkdvirtualenv py3`
  * `workon py3`
* Run `maturin build`
