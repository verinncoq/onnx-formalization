From Coq Require Import Strings.String.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import ZArith.

From CoqE2EAI Require Export error_option.
From CoqE2EAI Require Export model.
From CoqE2EAI Require Export matrices.
From CoqE2EAI Require Export relu.
From CoqE2EAI Require Export gemm.

(*computes wether a string occures in a given list*)
Fixpoint Inb (s: string) (l: list string) : bool :=
  match l with
  | [] => false
  | h::t => match eqb s h with
    | true => true
    | false => Inb s t
    end
  end.

(*computes wether a tensor has a given name*)
Definition tensor_has_name (name: string) (t: TensorProto) : bool :=
  match t with
  | TensorProto_constructor _ _ _ _ _ _ _ name_t_option _ _ _ _ _ _ _ => 
    match name_t_option with
    | Some name_t => eqb name name_t
    | None => false
    end
  end.

(*
Computes wether a vertex has a given name
The Type <vertex> is defined <in onnx_model_to_premodel>.
*)
Definition vertex_has_name (name: string) (v: vertex) : bool :=
  match v with
  | node (NodeProto_constructor _ outputs _ _ _ _ _ _ _ _) => Inb name outputs
  | tensor (TensorProto_constructor _ _ _ _ _ _ _ name_t_option _ _ _ _ _ _ _) => 
    match name_t_option with
    | Some name_t => eqb name name_t
    | None => false
    end
  | input (ValueInfoProto_constructor name_v_option _ _ _) => 
    match name_v_option with
    | Some name_v => eqb name name_v
    | None => false
    end
  | output (ValueInfoProto_constructor name_v_option _ _ _) => 
    match name_v_option with
    | Some name_v => eqb name name_v
    | None => false
    end
  end.

(*Finds vertices with name <name> in a given list*)
Definition find_vertex (vertices: list vertex) (name: string) : list vertex :=
  filter (vertex_has_name name) vertices.

(*
Recursive implementation of the onnx_evaluator.
Gets called maximum of <depth> times.
Is called on a list of user inputs, a list of vertices (the computational graph) and a specified vertex <evaluate> to be evaluated.
Depending on the Type of <evaluate>, it performs different actions:
  - Node:    Check op_type, evaluate all input vertices and compute if possible
  - Tensor:  Return itself
  - Input:   Search in user inputs for tensor with same name, if exactly one found: return it
  - Output:  Search in vertices for vertex with same name, if exactly one found: evaluate it
*)
Fixpoint onnx_evaluator_recursive (depth: nat) (user_inputs: list TensorProto) (vertices: list vertex) (evaluate: vertex) : error_option TensorProto :=
  match depth with
  | O => Error "ONNX Evaluator: Run out of vertices. Maybe a circular dependency, a missing vertex, or the list of nodes is not sorted topologically"
  | S n => (*check the type of the vertex to be evaluated*)
    match evaluate with
    (*Node: check op_type and compute it if possible*)
    | node (NodeProto_constructor node_inputs node_outputs _ op_type _ _ attributes _ _ _) => match op_type with

      | Some """Gemm""" => match node_inputs with (*check input amount*)
        | [node_input_A; node_input_B; node_input_C] => (*three inputs*)
          (*search for vertices with specified names and check if there are given and unique*)
          match find_vertex vertices node_input_A, find_vertex vertices node_input_B, find_vertex vertices node_input_C with
          | [vertex_A], [vertex_B], [vertex_C] => (*evaluate each vertex and compute gemm*)
            match
            onnx_evaluator_recursive n user_inputs vertices vertex_A,
            onnx_evaluator_recursive n user_inputs vertices vertex_B,
            onnx_evaluator_recursive n user_inputs vertices vertex_C
            with
            | Success A, Success B, Success C => gemm A B C attributes
            | Error e, _, _ => Error e
            | _, Error e, _ => Error e
            | _, _, Error e => Error e
            end
          | _, _, _ => Error ("ONNX Evaluator: found not exactly one vertex with name " ++
                       node_input_A ++ " or " ++ node_input_B ++ " or " ++ node_input_C)
          end
        | [node_input_A; node_input_B] => (*two inputs*)
          (*search for vertices with specified names and check if there are given and unique*)
          match find_vertex vertices node_input_A, find_vertex vertices node_input_B with
          | [vertex_A], [vertex_B] => (*evaluate each vertex and compute gemm*)
            match
            onnx_evaluator_recursive n user_inputs vertices vertex_A,
            onnx_evaluator_recursive n user_inputs vertices vertex_B
            with
            | Success A, Success B => gemm_two_inputs A B attributes
            | Error e, _ => Error e
            | _, Error e => Error e
            end
          | _, _ => Error ("ONNX Evaluator: found not exactly one vertex with name " ++
                       node_input_A ++ " or " ++ node_input_B)
          end
        | _ => Error "Gemm must have 2-3 inputs"
        end

      | Some """Relu""" => match node_inputs with (*check input amount*)
        | [node_input_name] =>
          (*search for vertex with specified name and check if it is given and unique*)
          match find_vertex vertices node_input_name with
          | [vertex] => (*evaluate each vertex and compute gemm*)
            match onnx_evaluator_recursive n user_inputs vertices vertex with
            | Success rec => relu.relu rec
            | Error e => Error e
            end
          | _ => Error ("ONNX Evaluator: found not exactly one vertex with name " ++ node_input_name)
          end
        | _ => Error "Relu must have exactly one input"
        end

      | Some type => Error ("ONNX Evaluator: op_type of NodeProto must be a valid, implemented operation, not " ++ type)
      | None => Error ("ONNX Evaluator: op_type of NodeProto must be non-empty")
      end

    (*Tensor: just return itself*)
    | tensor t => Success t

    (*Input: search in user_inputs for tensor with same name, if exactly one found: return it*)
    | input (ValueInfoProto_constructor name_option _ _ _) =>
      match name_option with
      | Some name => match filter (tensor_has_name name) user_inputs with
        | [user_input] => Success user_input
        | _ => Error ("ONNX Evaluator: not exactly one user input given for input vertex: " ++ name)
        end
      | None => Error "ONNX Evaluator: Input Vertex must define name"
      end

    (*Output: search in vertices for vertex with same name, if exactly one found: evaluate it*)
    | output (ValueInfoProto_constructor name_option _ _ _) =>
      match name_option with
      | Some name => match filter (vertex_has_name name) vertices with
        | [v] => onnx_evaluator_recursive n user_inputs vertices v
        | _ => Error ("ONNX Evaluator: not exaclty one vertex (node, initializer or input) found: " ++ name)
        end
      | None => Error "ONNX Evaluator: Output Vertex must define name"
      end

    end
  end.

(*Calls the recursive implementation of the onnx_evaluator on a model's graph*)
Definition onnx_evaluator (model: ModelProto) (user_inputs: list TensorProto) : error_option (list TensorProto) :=
  match model with
  | ModelProto_constructor _ _ _ _ _ _ _ graph_option _ _ _ _ =>
    match graph_option with
    | Some graph => match graph with
      | GraphProto_constructor nodes _ initializers _ _ inputs outputs _ _ _ =>
        let vertices := (map (fun x => node x) (rev nodes)) ++ (map (fun x => input x) inputs) ++ (map (fun x => tensor x) initializers) in
        let evaluate := onnx_evaluator_recursive (length vertices) user_inputs vertices in
        let output_vertices := map (fun x => output x) outputs in
        list_error_option_to_error_option_list (map evaluate output_vertices) []
      end
    | None => Error "ONNX Evaluator: Model must define a graph"
    end
  end.
