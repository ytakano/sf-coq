# Coq and Proof General

## Run Docker

```
$ docker-compose build
$ docker-compose run coq-cpdt
```

## Install Proof General on Emacs

Then, run ```M-x package-refresh-contents RET``` followed by
```M-x package-install RET proof-general RET``` to install and byte-compile proof-general.

Optionally, install company-coq as
```M-x Package-install RET company-coq RET```.

add .emacs
```
(add-hook 'coq-mode-hook #'company-coq-mode)
```
