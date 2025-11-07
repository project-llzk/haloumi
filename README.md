# haloumi: a unified IR extraction framework for Halo2 and PLONKish circuits

haloumi is a frontend for extracting the constraints from Halo2 circuits into LLZK and PCL. 

## Library agnostic

The framework is agnostic to specific Halo2 implementations and instead exposes a series of traits that the client
implements in order to integrate with the framework. This means that the framework is not limited to Halo2 per se,
any circuit building library that fits the conceptual model of Halo2 may be able to integrate with the framework.

Why is the framework library agnostic? Because developers that use Halo2 tend to fork the base library to better suit 
their needs. This means that the frontend cannot depend on a canonical Halo2 crate that pulls from crates.io.

## Usage

TBD

## Instalation

TBD
