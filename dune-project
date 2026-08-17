(lang dune 3.21)

(name onnxformalization)

(generate_opam_files true)

(source
 (github verinncoq/onnx-formalization))

(authors "Leo Gummersbach" "Andrei Aleksandrov" "Kim Völlinger")

(maintainers "Andrei Aleksandrov" "Kim Völlinger" "Alessandro Bruni" "Alistair Sirman")

(license APACHE-2.0)

(using rocq 0.11)

(package
 (name onnxformalization)
 (synopsis "ONNX Neural Networks: A Verified Import Pipeline for Rocq")
 (depends 
    (ocaml (="4.14.2")) 
    (rocq-core (="9.1.0")) 
    (coq-coquelicot (="3.4.4"))
    (coq-flocq (= "4.2.2")) ))
