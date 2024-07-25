(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter ic : G -> G.
Parameter icext : G -> G -> G.
Parameter iext : G -> G -> G -> G.
Parameter ifeq : G -> G -> G -> G -> G.
Parameter ip : G -> G.
Parameter ir : G -> G.
Parameter lv : G -> G.
Parameter true : G.
Parameter uri_rdf_Alt : G.
Parameter uri_rdf_Bag : G.
Parameter uri_rdf_List : G.
Parameter uri_rdf_Property : G.
Parameter uri_rdf_XMLLiteral : G.
Parameter uri_rdf__1 : G.
Parameter uri_rdf__2 : G.
Parameter uri_rdf__3 : G.
Parameter uri_rdf_first : G.
Parameter uri_rdf_nil : G.
Parameter uri_rdf_object : G.
Parameter uri_rdf_predicate : G.
Parameter uri_rdf_rest : G.
Parameter uri_rdf_subject : G.
Parameter uri_rdf_type : G.
Parameter uri_rdf_value : G.
Parameter uri_rdfs_Class : G.
Parameter uri_rdfs_Container : G.
Parameter uri_rdfs_ContainerMembershipProperty : G.
Parameter uri_rdfs_Datatype : G.
Parameter uri_rdfs_Literal : G.
Parameter uri_rdfs_Resource : G.
Parameter uri_rdfs_Seq : G.
Parameter uri_rdfs_Statement : G.
Parameter uri_rdfs_comment : G.
Parameter uri_rdfs_domain : G.
Parameter uri_rdfs_isDefinedBy : G.
Parameter uri_rdfs_label : G.
Parameter uri_rdfs_member : G.
Parameter uri_rdfs_range : G.
Parameter uri_rdfs_seeAlso : G.
Parameter uri_rdfs_subClassOf : G.
Parameter uri_rdfs_subPropertyOf : G.
Axiom rdfs_value_range : (iext uri_rdfs_range uri_rdf_value uri_rdfs_Resource) = true.
Axiom rdfs_value_domain : (iext uri_rdfs_domain uri_rdf_value uri_rdfs_Resource) = true.
Axiom rdfs_type_range : (iext uri_rdfs_range uri_rdf_type uri_rdfs_Class) = true.
Axiom rdfs_type_domain : (iext uri_rdfs_domain uri_rdf_type uri_rdfs_Resource) = true.
Axiom rdfs_subpropertyof_trans : forall P Q R : G, (ifeq (iext uri_rdfs_subPropertyOf Q R) true (ifeq (iext uri_rdfs_subPropertyOf P Q) true (iext uri_rdfs_subPropertyOf P R) true) true) = true.
Axiom rdfs_subpropertyof_reflex : forall P : G, (ifeq (ip P) true (iext uri_rdfs_subPropertyOf P P) true) = true.
Axiom rdfs_subpropertyof_range : (iext uri_rdfs_range uri_rdfs_subPropertyOf uri_rdf_Property) = true.
Axiom rdfs_subpropertyof_main : forall P Q X Y : G, (ifeq (iext uri_rdfs_subPropertyOf P Q) true (ifeq (iext P X Y) true (iext Q X Y) true) true) = true.
Axiom rdfs_subpropertyof_main_1 : forall P Q : G, (ifeq (iext uri_rdfs_subPropertyOf P Q) true (ip P) true) = true.
Axiom rdfs_subpropertyof_main_2 : forall P Q : G, (ifeq (iext uri_rdfs_subPropertyOf P Q) true (ip Q) true) = true.
Axiom rdfs_subpropertyof_domain : (iext uri_rdfs_domain uri_rdfs_subPropertyOf uri_rdf_Property) = true.
Axiom rdfs_subclassof_trans : forall C D E : G, (ifeq (iext uri_rdfs_subClassOf D E) true (ifeq (iext uri_rdfs_subClassOf C D) true (iext uri_rdfs_subClassOf C E) true) true) = true.
Axiom rdfs_subclassof_reflex : forall C : G, (ifeq (ic C) true (iext uri_rdfs_subClassOf C C) true) = true.
Axiom rdfs_subclassof_range : (iext uri_rdfs_range uri_rdfs_subClassOf uri_rdfs_Class) = true.
Axiom rdfs_subclassof_main : forall C D : G, (ifeq (iext uri_rdfs_subClassOf C D) true (ic C) true) = true.
Axiom rdfs_subclassof_main_1 : forall C D : G, (ifeq (iext uri_rdfs_subClassOf C D) true (ic D) true) = true.
Axiom rdfs_subclassof_main_2 : forall C D X : G, (ifeq (icext C X) true (ifeq (iext uri_rdfs_subClassOf C D) true (icext D X) true) true) = true.
Axiom rdfs_subclassof_domain : (iext uri_rdfs_domain uri_rdfs_subClassOf uri_rdfs_Class) = true.
Axiom rdfs_reification_subject_range : (iext uri_rdfs_range uri_rdf_subject uri_rdfs_Resource) = true.
Axiom rdfs_reification_subject_domain : (iext uri_rdfs_domain uri_rdf_subject uri_rdfs_Statement) = true.
Axiom rdfs_reification_predicate_range : (iext uri_rdfs_range uri_rdf_predicate uri_rdfs_Resource) = true.
Axiom rdfs_reification_predicate_domain : (iext uri_rdfs_domain uri_rdf_predicate uri_rdfs_Statement) = true.
Axiom rdfs_reification_object_range : (iext uri_rdfs_range uri_rdf_predicate uri_rdfs_Resource) = true.
Axiom rdfs_reification_object_domain : (iext uri_rdfs_domain uri_rdf_object uri_rdfs_Statement) = true.
Axiom rdfs_range_range : (iext uri_rdfs_range uri_rdfs_range uri_rdfs_Class) = true.
Axiom rdfs_range_main : forall C P X Y : G, (ifeq (iext uri_rdfs_range P C) true (ifeq (iext P X Y) true (icext C Y) true) true) = true.
Axiom rdfs_range_domain : (iext uri_rdfs_domain uri_rdfs_range uri_rdf_Property) = true.
Axiom rdfs_property_type : (iext uri_rdf_type uri_rdf_Property uri_rdfs_Class) = true.
Axiom rdfs_lv_def : forall X : G, (ifeq (lv X) true (icext uri_rdfs_Literal X) true) = true.
Axiom rdfs_lv_def_1 : forall X : G, (ifeq (icext uri_rdfs_Literal X) true (lv X) true) = true.
Axiom rdfs_ir_def : forall X : G, (ifeq (ir X) true (icext uri_rdfs_Resource X) true) = true.
Axiom rdfs_ir_def_1 : forall X : G, (ifeq (icext uri_rdfs_Resource X) true (ir X) true) = true.
Axiom rdfs_ic_def : forall X : G, (ifeq (icext uri_rdfs_Class X) true (ic X) true) = true.
Axiom rdfs_ic_def_1 : forall X : G, (ifeq (ic X) true (icext uri_rdfs_Class X) true) = true.
Axiom rdfs_domain_range : (iext uri_rdfs_range uri_rdfs_domain uri_rdfs_Class) = true.
Axiom rdfs_domain_main : forall C P X Y : G, (ifeq (iext uri_rdfs_domain P C) true (ifeq (iext P X Y) true (icext C X) true) true) = true.
Axiom rdfs_domain_domain : (iext uri_rdfs_domain uri_rdfs_domain uri_rdf_Property) = true.
Axiom rdfs_datatype_sub : (iext uri_rdfs_subClassOf uri_rdfs_Datatype uri_rdfs_Class) = true.
Axiom rdfs_datatype_instsub_literal : forall D : G, (ifeq (icext uri_rdfs_Datatype D) true (iext uri_rdfs_subClassOf D uri_rdfs_Literal) true) = true.
Axiom rdfs_dat_xmlliteral_type : (iext uri_rdf_type uri_rdf_XMLLiteral uri_rdfs_Datatype) = true.
Axiom rdfs_dat_xmlliteral_sub : (iext uri_rdfs_subClassOf uri_rdf_XMLLiteral uri_rdfs_Literal) = true.
Axiom rdfs_container_seq_sub : (iext uri_rdfs_subClassOf uri_rdfs_Seq uri_rdfs_Container) = true.
Axiom rdfs_container_n_type_003 : (iext uri_rdf_type uri_rdf__3 uri_rdfs_ContainerMembershipProperty) = true.
Axiom rdfs_container_n_type_002 : (iext uri_rdf_type uri_rdf__2 uri_rdfs_ContainerMembershipProperty) = true.
Axiom rdfs_container_n_type_001 : (iext uri_rdf_type uri_rdf__1 uri_rdfs_ContainerMembershipProperty) = true.
Axiom rdfs_container_n_range_003 : (iext uri_rdfs_range uri_rdf__3 uri_rdfs_Resource) = true.
Axiom rdfs_container_n_range_002 : (iext uri_rdfs_range uri_rdf__2 uri_rdfs_Resource) = true.
Axiom rdfs_container_n_range_001 : (iext uri_rdfs_range uri_rdf__1 uri_rdfs_Resource) = true.
Axiom rdfs_container_n_domain_003 : (iext uri_rdfs_domain uri_rdf__3 uri_rdfs_Resource) = true.
Axiom rdfs_container_n_domain_002 : (iext uri_rdfs_domain uri_rdf__2 uri_rdfs_Resource) = true.
Axiom rdfs_container_n_domain_001 : (iext uri_rdfs_domain uri_rdf__1 uri_rdfs_Resource) = true.
Axiom rdfs_container_member_range : (iext uri_rdfs_range uri_rdfs_member uri_rdfs_Resource) = true.
Axiom rdfs_container_member_domain : (iext uri_rdfs_domain uri_rdfs_member uri_rdfs_Resource) = true.
Axiom rdfs_container_containermembershipproperty_sub : (iext uri_rdfs_subClassOf uri_rdfs_ContainerMembershipProperty uri_rdf_Property) = true.
Axiom rdfs_container_containermembershipproperty_instsub_member : forall P : G, (ifeq (icext uri_rdfs_ContainerMembershipProperty P) true (iext uri_rdfs_subPropertyOf P uri_rdfs_member) true) = true.
Axiom rdfs_container_bag_sub : (iext uri_rdfs_subClassOf uri_rdf_Bag uri_rdfs_Container) = true.
Axiom rdfs_container_alt_sub : (iext uri_rdfs_subClassOf uri_rdf_Alt uri_rdfs_Container) = true.
Axiom rdfs_collection_rest_range : (iext uri_rdfs_range uri_rdf_rest uri_rdf_List) = true.
Axiom rdfs_collection_rest_domain : (iext uri_rdfs_domain uri_rdf_rest uri_rdf_List) = true.
Axiom rdfs_collection_first_range : (iext uri_rdfs_range uri_rdf_first uri_rdfs_Resource) = true.
Axiom rdfs_collection_first_domain : (iext uri_rdfs_domain uri_rdf_first uri_rdf_List) = true.
Axiom rdfs_class_instsub_resource : forall C : G, (ifeq (ic C) true (iext uri_rdfs_subClassOf C uri_rdfs_Resource) true) = true.
Axiom rdfs_cext_def : forall C X : G, (ifeq (iext uri_rdf_type X C) true (icext C X) true) = true.
Axiom rdfs_cext_def_1 : forall C X : G, (ifeq (icext C X) true (iext uri_rdf_type X C) true) = true.
Axiom rdfs_annotation_seealso_range : (iext uri_rdfs_range uri_rdfs_seeAlso uri_rdfs_Resource) = true.
Axiom rdfs_annotation_seealso_domain : (iext uri_rdfs_domain uri_rdfs_seeAlso uri_rdfs_Resource) = true.
Axiom rdfs_annotation_label_range : (iext uri_rdfs_range uri_rdfs_label uri_rdfs_Literal) = true.
Axiom rdfs_annotation_label_domain : (iext uri_rdfs_domain uri_rdfs_label uri_rdfs_Resource) = true.
Axiom rdfs_annotation_isdefinedby_sub : (iext uri_rdfs_subPropertyOf uri_rdfs_isDefinedBy uri_rdfs_seeAlso) = true.
Axiom rdfs_annotation_isdefinedby_range : (iext uri_rdfs_range uri_rdfs_isDefinedBy uri_rdfs_Resource) = true.
Axiom rdfs_annotation_isdefinedby_domain : (iext uri_rdfs_domain uri_rdfs_isDefinedBy uri_rdfs_Resource) = true.
Axiom rdfs_annotation_comment_range : (iext uri_rdfs_range uri_rdfs_comment uri_rdfs_Literal) = true.
Axiom rdfs_annotation_comment_domain : (iext uri_rdfs_domain uri_rdfs_comment uri_rdfs_Resource) = true.
Axiom rdf_value_type : (iext uri_rdf_type uri_rdf_type uri_rdf_Property) = true.
Axiom rdf_type_type : (iext uri_rdf_type uri_rdf_type uri_rdf_Property) = true.
Axiom rdf_type_ip : forall P : G, (ifeq (iext uri_rdf_type P uri_rdf_Property) true (ip P) true) = true.
Axiom rdf_type_ip_1 : forall P : G, (ifeq (ip P) true (iext uri_rdf_type P uri_rdf_Property) true) = true.
Axiom rdf_reification_subject_type : (iext uri_rdf_type uri_rdf_subject uri_rdf_Property) = true.
Axiom rdf_reification_predicate_type : (iext uri_rdf_type uri_rdf_value uri_rdf_Property) = true.
Axiom rdf_reification_object_type : (iext uri_rdf_type uri_rdf_object uri_rdf_Property) = true.
Axiom rdf_container_n_type_003 : (iext uri_rdf_type uri_rdf__3 uri_rdf_Property) = true.
Axiom rdf_container_n_type_002 : (iext uri_rdf_type uri_rdf__2 uri_rdf_Property) = true.
Axiom rdf_container_n_type_001 : (iext uri_rdf_type uri_rdf__1 uri_rdf_Property) = true.
Axiom rdf_collection_rest_type : (iext uri_rdf_type uri_rdf_rest uri_rdf_Property) = true.
Axiom rdf_collection_nil_type : (iext uri_rdf_type uri_rdf_nil uri_rdf_List) = true.
Axiom rdf_collection_first_type : (iext uri_rdf_type uri_rdf_first uri_rdf_Property) = true.
Axiom simple_lv : forall X : G, (ifeq (lv X) true (ir X) true) = true.
Axiom simple_ir : forall X : G, (ir X) = true.
Axiom simple_iext_property : forall O P S : G, (ifeq (iext P S O) true (ip P) true) = true.
Axiom ifeq_axiom : forall A B C : G, (ifeq A A B C) = B.


(* Goal *)
Theorem check : (tuple (iext uri_rdfs_subClassOf uri_owl_Class uri_owl_Thing) (iext uri_rdfs_subClassOf uri_rdfs_Datatype uri_owl_Class) (iext uri_rdf_type uri_owl_Class uri_owl_Class) (iext uri_rdf_type uri_owl_Class uri_owl_Thing) (iext uri_owl_equivalentClass uri_owl_Class uri_rdfs_Class)) = (tuple true true true true true).
Proof.
  hammer.
Qed.

Check check.
