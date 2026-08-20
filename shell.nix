{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  buildInputs = [
    (pkgs.rocq-core.override { version = "9.1.0"; })
    pkgs.python3
    pkgs.python3Packages.pip
  ];
}