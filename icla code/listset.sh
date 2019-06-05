#!/bin/bash

echo ‘GenReflect
coqc GenReflect.v

echo ’SetSpecs
coqc SetSpecs.v

echo ’Sorting
coqc Sorting.v

echo ‘MinMax
coqc MinMax.v

echo ‘DecType
coqc DecType.v

echo ‘SetReflect
coqc SetReflect.v

echo ‘DecList
coqc DecList.v

echo ‘MoreDecList
coqc MoreDecList.v

echo ‘OrdType
coqc OrdType.v

echo ‘OrdList.v
coqc OrdList.v

echo ‘OrdSet
coqc OrdSet.v

echo ‘SetMaps
coqc SetMaps.v

echo ‘Powerset
coqc Powerset.v
