(* Zenerated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable ic : Z -> Z.
Variable icext : Z -> Z -> Z.
Variable iext : Z -> Z -> Z -> Z.
Variable ifeq : Z -> Z -> Z -> Z -> Z.
Variable ip : Z -> Z.
Variable ir : Z -> Z.
Variable lv : Z -> Z.
Variable true : Z.
Variable uri_rdf_Alt : Z.
Variable uri_rdf_Bag : Z.
Variable uri_rdf_List : Z.
Variable uri_rdf_Property : Z.
Variable uri_rdf_XMLLiteral : Z.
Variable uri_rdf__1 : Z.
Variable uri_rdf__2 : Z.
Variable uri_rdf__3 : Z.
Variable uri_rdf_first : Z.
Variable uri_rdf_nil : Z.
Variable uri_rdf_object : Z.
Variable uri_rdf_predicate : Z.
Variable uri_rdf_rest : Z.
Variable uri_rdf_subject : Z.
Variable uri_rdf_type : Z.
Variable uri_rdf_value : Z.
Variable uri_rdfs_Class : Z.
Variable uri_rdfs_Container : Z.
Variable uri_rdfs_ContainerMembershipProperty : Z.
Variable uri_rdfs_Datatype : Z.
Variable uri_rdfs_Literal : Z.
Variable uri_rdfs_Resource : Z.
Variable uri_rdfs_Seq : Z.
Variable uri_rdfs_Statement : Z.
Variable uri_rdfs_comment : Z.
Variable uri_rdfs_domain : Z.
Variable uri_rdfs_isDefinedBy : Z.
Variable uri_rdfs_label : Z.
Variable uri_rdfs_member : Z.
Variable uri_rdfs_range : Z.
Variable uri_rdfs_seeAlso : Z.
Variable uri_rdfs_subClassOf : Z.
Variable uri_rdfs_subPropertyOf : Z.
Axiom rdfs_value_range : (iext uri_rdfs_range uri_rdf_value uri_rdfs_Resource) =? true.
Axiom rdfs_value_domain : (iext uri_rdfs_domain uri_rdf_value uri_rdfs_Resource) =? true.
Axiom rdfs_type_range : (iext uri_rdfs_range uri_rdf_type uri_rdfs_Class) =? true.
Axiom rdfs_type_domain : (iext uri_rdfs_domain uri_rdf_type uri_rdfs_Resource) =? true.
Axiom rdfs_subpropertyof_trans : forall P Q R : Z, (ifeq (iext uri_rdfs_subPropertyOf Q R) true (ifeq (iext uri_rdfs_subPropertyOf P Q) true (iext uri_rdfs_subPropertyOf P R) true) true) =? true.
Axiom rdfs_subpropertyof_reflex : forall P : Z, (ifeq (ip P) true (iext uri_rdfs_subPropertyOf P P) true) =? true.
Axiom rdfs_subpropertyof_range : (iext uri_rdfs_range uri_rdfs_subPropertyOf uri_rdf_Property) =? true.
Axiom rdfs_subpropertyof_main : forall P Q X Y : Z, (ifeq (iext uri_rdfs_subPropertyOf P Q) true (ifeq (iext P X Y) true (iext Q X Y) true) true) =? true.
Axiom rdfs_subpropertyof_main_1 : forall P Q : Z, (ifeq (iext uri_rdfs_subPropertyOf P Q) true (ip P) true) =? true.
Axiom rdfs_subpropertyof_main_2 : forall P Q : Z, (ifeq (iext uri_rdfs_subPropertyOf P Q) true (ip Q) true) =? true.
Axiom rdfs_subpropertyof_domain : (iext uri_rdfs_domain uri_rdfs_subPropertyOf uri_rdf_Property) =? true.
Axiom rdfs_subclassof_trans : forall C D E : Z, (ifeq (iext uri_rdfs_subClassOf D E) true (ifeq (iext uri_rdfs_subClassOf C D) true (iext uri_rdfs_subClassOf C E) true) true) =? true.
Axiom rdfs_subclassof_reflex : forall C : Z, (ifeq (ic C) true (iext uri_rdfs_subClassOf C C) true) =? true.
Axiom rdfs_subclassof_range : (iext uri_rdfs_range uri_rdfs_subClassOf uri_rdfs_Class) =? true.
Axiom rdfs_subclassof_main : forall C D : Z, (ifeq (iext uri_rdfs_subClassOf C D) true (ic C) true) =? true.
Axiom rdfs_subclassof_main_1 : forall C D : Z, (ifeq (iext uri_rdfs_subClassOf C D) true (ic D) true) =? true.
Axiom rdfs_subclassof_main_2 : forall C D X : Z, (ifeq (icext C X) true (ifeq (iext uri_rdfs_subClassOf C D) true (icext D X) true) true) =? true.
Axiom rdfs_subclassof_domain : (iext uri_rdfs_domain uri_rdfs_subClassOf uri_rdfs_Class) =? true.
Axiom rdfs_reification_subject_range : (iext uri_rdfs_range uri_rdf_subject uri_rdfs_Resource) =? true.
Axiom rdfs_reification_subject_domain : (iext uri_rdfs_domain uri_rdf_subject uri_rdfs_Statement) =? true.
Axiom rdfs_reification_predicate_range : (iext uri_rdfs_range uri_rdf_predicate uri_rdfs_Resource) =? true.
Axiom rdfs_reification_predicate_domain : (iext uri_rdfs_domain uri_rdf_predicate uri_rdfs_Statement) =? true.
Axiom rdfs_reification_object_range : (iext uri_rdfs_range uri_rdf_predicate uri_rdfs_Resource) =? true.
Axiom rdfs_reification_object_domain : (iext uri_rdfs_domain uri_rdf_object uri_rdfs_Statement) =? true.
Axiom rdfs_range_range : (iext uri_rdfs_range uri_rdfs_range uri_rdfs_Class) =? true.
Axiom rdfs_range_main : forall C P X Y : Z, (ifeq (iext uri_rdfs_range P C) true (ifeq (iext P X Y) true (icext C Y) true) true) =? true.
Axiom rdfs_range_domain : (iext uri_rdfs_domain uri_rdfs_range uri_rdf_Property) =? true.
Axiom rdfs_property_type : (iext uri_rdf_type uri_rdf_Property uri_rdfs_Class) =? true.
Axiom rdfs_lv_def : forall X : Z, (ifeq (lv X) true (icext uri_rdfs_Literal X) true) =? true.
Axiom rdfs_lv_def_1 : forall X : Z, (ifeq (icext uri_rdfs_Literal X) true (lv X) true) =? true.
Axiom rdfs_ir_def : forall X : Z, (ifeq (ir X) true (icext uri_rdfs_Resource X) true) =? true.
Axiom rdfs_ir_def_1 : forall X : Z, (ifeq (icext uri_rdfs_Resource X) true (ir X) true) =? true.
Axiom rdfs_ic_def : forall X : Z, (ifeq (icext uri_rdfs_Class X) true (ic X) true) =? true.
Axiom rdfs_ic_def_1 : forall X : Z, (ifeq (ic X) true (icext uri_rdfs_Class X) true) =? true.
Axiom rdfs_domain_range : (iext uri_rdfs_range uri_rdfs_domain uri_rdfs_Class) =? true.
Axiom rdfs_domain_main : forall C P X Y : Z, (ifeq (iext uri_rdfs_domain P C) true (ifeq (iext P X Y) true (icext C X) true) true) =? true.
Axiom rdfs_domain_domain : (iext uri_rdfs_domain uri_rdfs_domain uri_rdf_Property) =? true.
Axiom rdfs_datatype_sub : (iext uri_rdfs_subClassOf uri_rdfs_Datatype uri_rdfs_Class) =? true.
Axiom rdfs_datatype_instsub_literal : forall D : Z, (ifeq (icext uri_rdfs_Datatype D) true (iext uri_rdfs_subClassOf D uri_rdfs_Literal) true) =? true.
Axiom rdfs_dat_xmlliteral_type : (iext uri_rdf_type uri_rdf_XMLLiteral uri_rdfs_Datatype) =? true.
Axiom rdfs_dat_xmlliteral_sub : (iext uri_rdfs_subClassOf uri_rdf_XMLLiteral uri_rdfs_Literal) =? true.
Axiom rdfs_container_seq_sub : (iext uri_rdfs_subClassOf uri_rdfs_Seq uri_rdfs_Container) =? true.
Axiom rdfs_container_n_type_003 : (iext uri_rdf_type uri_rdf__3 uri_rdfs_ContainerMembershipProperty) =? true.
Axiom rdfs_container_n_type_002 : (iext uri_rdf_type uri_rdf__2 uri_rdfs_ContainerMembershipProperty) =? true.
Axiom rdfs_container_n_type_001 : (iext uri_rdf_type uri_rdf__1 uri_rdfs_ContainerMembershipProperty) =? true.
Axiom rdfs_container_n_range_003 : (iext uri_rdfs_range uri_rdf__3 uri_rdfs_Resource) =? true.
Axiom rdfs_container_n_range_002 : (iext uri_rdfs_range uri_rdf__2 uri_rdfs_Resource) =? true.
Axiom rdfs_container_n_range_001 : (iext uri_rdfs_range uri_rdf__1 uri_rdfs_Resource) =? true.
Axiom rdfs_container_n_domain_003 : (iext uri_rdfs_domain uri_rdf__3 uri_rdfs_Resource) =? true.
Axiom rdfs_container_n_domain_002 : (iext uri_rdfs_domain uri_rdf__2 uri_rdfs_Resource) =? true.
Axiom rdfs_container_n_domain_001 : (iext uri_rdfs_domain uri_rdf__1 uri_rdfs_Resource) =? true.
Axiom rdfs_container_member_range : (iext uri_rdfs_range uri_rdfs_member uri_rdfs_Resource) =? true.
Axiom rdfs_container_member_domain : (iext uri_rdfs_domain uri_rdfs_member uri_rdfs_Resource) =? true.
Axiom rdfs_container_containermembershipproperty_sub : (iext uri_rdfs_subClassOf uri_rdfs_ContainerMembershipProperty uri_rdf_Property) =? true.
Axiom rdfs_container_containermembershipproperty_instsub_member : forall P : Z, (ifeq (icext uri_rdfs_ContainerMembershipProperty P) true (iext uri_rdfs_subPropertyOf P uri_rdfs_member) true) =? true.
Axiom rdfs_container_bag_sub : (iext uri_rdfs_subClassOf uri_rdf_Bag uri_rdfs_Container) =? true.
Axiom rdfs_container_alt_sub : (iext uri_rdfs_subClassOf uri_rdf_Alt uri_rdfs_Container) =? true.
Axiom rdfs_collection_rest_range : (iext uri_rdfs_range uri_rdf_rest uri_rdf_List) =? true.
Axiom rdfs_collection_rest_domain : (iext uri_rdfs_domain uri_rdf_rest uri_rdf_List) =? true.
Axiom rdfs_collection_first_range : (iext uri_rdfs_range uri_rdf_first uri_rdfs_Resource) =? true.
Axiom rdfs_collection_first_domain : (iext uri_rdfs_domain uri_rdf_first uri_rdf_List) =? true.
Axiom rdfs_class_instsub_resource : forall C : Z, (ifeq (ic C) true (iext uri_rdfs_subClassOf C uri_rdfs_Resource) true) =? true.
Axiom rdfs_cext_def : forall C X : Z, (ifeq (iext uri_rdf_type X C) true (icext C X) true) =? true.
Axiom rdfs_cext_def_1 : forall C X : Z, (ifeq (icext C X) true (iext uri_rdf_type X C) true) =? true.
Axiom rdfs_annotation_seealso_range : (iext uri_rdfs_range uri_rdfs_seeAlso uri_rdfs_Resource) =? true.
Axiom rdfs_annotation_seealso_domain : (iext uri_rdfs_domain uri_rdfs_seeAlso uri_rdfs_Resource) =? true.
Axiom rdfs_annotation_label_range : (iext uri_rdfs_range uri_rdfs_label uri_rdfs_Literal) =? true.
Axiom rdfs_annotation_label_domain : (iext uri_rdfs_domain uri_rdfs_label uri_rdfs_Resource) =? true.
Axiom rdfs_annotation_isdefinedby_sub : (iext uri_rdfs_subPropertyOf uri_rdfs_isDefinedBy uri_rdfs_seeAlso) =? true.
Axiom rdfs_annotation_isdefinedby_range : (iext uri_rdfs_range uri_rdfs_isDefinedBy uri_rdfs_Resource) =? true.
Axiom rdfs_annotation_isdefinedby_domain : (iext uri_rdfs_domain uri_rdfs_isDefinedBy uri_rdfs_Resource) =? true.
Axiom rdfs_annotation_comment_range : (iext uri_rdfs_range uri_rdfs_comment uri_rdfs_Literal) =? true.
Axiom rdfs_annotation_comment_domain : (iext uri_rdfs_domain uri_rdfs_comment uri_rdfs_Resource) =? true.
Axiom rdf_value_type : (iext uri_rdf_type uri_rdf_type uri_rdf_Property) =? true.
Axiom rdf_type_type : (iext uri_rdf_type uri_rdf_type uri_rdf_Property) =? true.
Axiom rdf_type_ip : forall P : Z, (ifeq (iext uri_rdf_type P uri_rdf_Property) true (ip P) true) =? true.
Axiom rdf_type_ip_1 : forall P : Z, (ifeq (ip P) true (iext uri_rdf_type P uri_rdf_Property) true) =? true.
Axiom rdf_reification_subject_type : (iext uri_rdf_type uri_rdf_subject uri_rdf_Property) =? true.
Axiom rdf_reification_predicate_type : (iext uri_rdf_type uri_rdf_value uri_rdf_Property) =? true.
Axiom rdf_reification_object_type : (iext uri_rdf_type uri_rdf_object uri_rdf_Property) =? true.
Axiom rdf_container_n_type_003 : (iext uri_rdf_type uri_rdf__3 uri_rdf_Property) =? true.
Axiom rdf_container_n_type_002 : (iext uri_rdf_type uri_rdf__2 uri_rdf_Property) =? true.
Axiom rdf_container_n_type_001 : (iext uri_rdf_type uri_rdf__1 uri_rdf_Property) =? true.
Axiom rdf_collection_rest_type : (iext uri_rdf_type uri_rdf_rest uri_rdf_Property) =? true.
Axiom rdf_collection_nil_type : (iext uri_rdf_type uri_rdf_nil uri_rdf_List) =? true.
Axiom rdf_collection_first_type : (iext uri_rdf_type uri_rdf_first uri_rdf_Property) =? true.
Axiom simple_lv : forall X : Z, (ifeq (lv X) true (ir X) true) =? true.
Axiom simple_ir : forall X : Z, (ir X) =? true.
Axiom simple_iext_property : forall O P S : Z, (ifeq (iext P S O) true (ip P) true) =? true.
Axiom ifeq_axiom : forall A B C : Z, (ifeq A A B C) =? B.

Add_lemmas rdfs_value_range rdfs_value_domain rdfs_type_range rdfs_type_domain rdfs_subpropertyof_trans rdfs_subpropertyof_reflex rdfs_subpropertyof_range rdfs_subpropertyof_main rdfs_subpropertyof_main_1 rdfs_subpropertyof_main_2 rdfs_subpropertyof_domain rdfs_subclassof_trans rdfs_subclassof_reflex rdfs_subclassof_range rdfs_subclassof_main rdfs_subclassof_main_1 rdfs_subclassof_main_2 rdfs_subclassof_domain rdfs_reification_subject_range rdfs_reification_subject_domain rdfs_reification_predicate_range rdfs_reification_predicate_domain rdfs_reification_object_range rdfs_reification_object_domain rdfs_range_range rdfs_range_main rdfs_range_domain rdfs_property_type rdfs_lv_def rdfs_lv_def_1 rdfs_ir_def rdfs_ir_def_1 rdfs_ic_def rdfs_ic_def_1 rdfs_domain_range rdfs_domain_main rdfs_domain_domain rdfs_datatype_sub rdfs_datatype_instsub_literal rdfs_dat_xmlliteral_type rdfs_dat_xmlliteral_sub rdfs_container_seq_sub rdfs_container_n_type_003 rdfs_container_n_type_002 rdfs_container_n_type_001 rdfs_container_n_range_003 rdfs_container_n_range_002 rdfs_container_n_range_001 rdfs_container_n_domain_003 rdfs_container_n_domain_002 rdfs_container_n_domain_001 rdfs_container_member_range rdfs_container_member_domain rdfs_container_containermembershipproperty_sub rdfs_container_containermembershipproperty_instsub_member rdfs_container_bag_sub rdfs_container_alt_sub rdfs_collection_rest_range rdfs_collection_rest_domain rdfs_collection_first_range rdfs_collection_first_domain rdfs_class_instsub_resource rdfs_cext_def rdfs_cext_def_1 rdfs_annotation_seealso_range rdfs_annotation_seealso_domain rdfs_annotation_label_range rdfs_annotation_label_domain rdfs_annotation_isdefinedby_sub rdfs_annotation_isdefinedby_range rdfs_annotation_isdefinedby_domain rdfs_annotation_comment_range rdfs_annotation_comment_domain rdf_value_type rdf_type_type rdf_type_ip rdf_type_ip_1 rdf_reification_subject_type rdf_reification_predicate_type rdf_reification_object_type rdf_container_n_type_003 rdf_container_n_type_002 rdf_container_n_type_001 rdf_collection_rest_type rdf_collection_nil_type rdf_collection_first_type simple_lv simple_ir simple_iext_property ifeq_axiom.

(* Zoal *)
Theorem check : (tuple (iext uri_rdfs_subClassOf uri_owl_Class uri_owl_Thing) (iext uri_rdfs_subClassOf uri_rdfs_Datatype uri_owl_Class) (iext uri_rdf_type uri_owl_Class uri_owl_Class) (iext uri_rdf_type uri_owl_Class uri_owl_Thing) (iext uri_owl_equivalentClass uri_owl_Class uri_rdfs_Class)) =? (tuple true true true true true).
Proof.
  smt.
Qed.

Check check.

