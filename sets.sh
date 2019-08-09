#!/bin/bash

printf ‘GenReflect
coqc GenReflect.v
  
printf ‘SetSpecs 
coqc SetSpecs.v

printf ‘Sorting 
coqc Sorting.v

printf ‘MinMax 
coqc MinMax.v

printf ‘DecType
coqc DecType.v
 
printf ‘SetReflect
coqc SetReflect.v

printf ‘DecList
coqc DecList.v
 
printf ‘OrdType 
coqc OrdType.v

printf ‘OrdList 
coqc OrdList.v

printf ‘OrdSet 
coqc OrdSet.v

printf ‘SetMaps
coqc SetMaps.v
  
printf ‘Powerset
coqc Powerset.v

printf ‘SetCover
coqc SetCover.v
 
echo \
