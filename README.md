# The protocol's Tamarin Prover Code 

## Overview

This repository contains the Tamarin Prover code related to the security protocol verification discussed in our paper titled **“An Enhanced Security Protocol for Vehicular Adhoc Networks.”** The Tamarin Prover is a powerful tool for analyzing cryptographic protocols and verifying their security properties.

## Installation and Usage
For detailed installation instructions and usage guidelines, refer to [Chapter 2 of the Tamarin Prover manual](https://tamarin-prover.github.io/manual/master/book/002_installation.html).

## How to run the code
`Formal_Verifiaction.spthy`: Contains our protocol's Tamarin Prover source code. 
Then run the model via the command line tool:

`tamarin-prover interactive Formal_Verifiaction.spthy`

Then, you can just open the generated link in your browser. The link will be something like this:

`http://localhost:3001`

## Results

To check the model, open the Tamarin GUI and choose the correct file. Once the tab opens, you can find the model code on the left.

To prove a lemma, click "sorry" at the bottom of the lemma you want to prove. This will open the "Visualization display". You can check all lemmas by clicking "a. autoprove".

Depending on whether a lemma makes an "exists trace" statement or an "all traces" statement, different results indicate success. For proving an "exists trace" statement, Tamarin will output a trace (as a picture) that shows a fulfilling trace for the lemma. Proving an "all traces" statement means that Tamarin finds no trace that contradicts the statement.

Lemmas that can be proven will display a green trace on the left and, in the case of "exists trace" lemmas, a picture of a fulfilling trace. Lemmas that can be disproven will display a red trace on the left and, in the case of "all traces" lemmas, a picture of a contradicting trace.



