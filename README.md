Metacircular evaluator from chapter 4 of STRUCTURE AND                      
INTERPRETATION OF COMPUTER PROGRAMS (2nd edition)                           
                                                                            
Modified by kwn, 3/4/97                                                     
Modified and commented by Carl Offner, 10/21/98 -- 10/12/04                 
Modified and commented by JTan, 10/24/17                               

This code is the code for the metacircular evaluator as it appears          
in the textbook in sections 4.1.1-4.1.4, with the following                 
changes:                                                                    
                                                                             
1.  It uses #f and #t, not false and true, to be Scheme-conformant.         
                                                                           
2.  Some function names were changed to avoid conflict with the             
underlying Scheme:                                                          
                                                                            
         eval => xeval                                                         
         apply => xapply                                                       
        extend-environment => xtend-environment                               
                                                                        
3.  The driver-loop is called s450.                                         
                                                                         
4.  The booleans (#t and #f) are classified as self-evaluating.             
                                                                            
 5.  These modifications make it look more like UMB Scheme:                  
                                                                         
    The define special form evaluates to (i.e., "returns") the           
    variable being defined.                                            
    No prefix is printed before an output value.                         
                                                                           
6.  I changed "compound-procedure" to "user-defined-procedure"
