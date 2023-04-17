// SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.4.16 <0.8.7;

contract CertificateManager{    
    
    event newCertificateIssued(string _cert_id, string _pf_id, string _reg_name, string _evaluator_name, uint256 _score);
    
    struct Portfolio_Cert{
        string cert_id;
        string pf_id;
        string pf_name;
        string reg_name;
        string organizationID;
        string evaluator_name;
        uint256 score;
        string evaluator_pk;
        string cert_Hash;
        string certIssuedTimestamp;
        string cert_url;
        bool isValid;
    }
    
    mapping(string => Portfolio_Cert) Portfolio_Certs;
    string[] public Portfolio_CertList;
    
    function issuePortfolioCertificate(
        string memory _cert_id,
        string memory _pf_id,
        string memory _pf_name,
        string memory _reg_name,
        string memory _organizationID,
        string memory _evaluator_name,
        uint256 _score,
        string memory _evaluator_pk,
        string memory _cert_Hash,
        string memory _certIssuedTimestamp,
        string memory _cert_url,
        bool _isValid) 
        public{
            Portfolio_Certs[_cert_id].pf_id = _pf_id;
            Portfolio_Certs[_cert_id].pf_name = _pf_name;
            Portfolio_Certs[_cert_id].reg_name = _reg_name;
            Portfolio_Certs[_cert_id].organizationID = _organizationID;
            Portfolio_Certs[_cert_id].evaluator_name = _evaluator_name;
            Portfolio_Certs[_cert_id].score = _score;
            Portfolio_Certs[_cert_id].evaluator_pk = _evaluator_pk;
            Portfolio_Certs[_cert_id].cert_Hash = _cert_Hash;
            Portfolio_Certs[_cert_id].certIssuedTimestamp = _certIssuedTimestamp;
            Portfolio_Certs[_cert_id].cert_url = _cert_url;
            Portfolio_Certs[_cert_id].isValid = _isValid;
            
            Portfolio_CertList.push(_cert_id);
            
            emit newCertificateIssued(_cert_id, _pf_id, _reg_name, _evaluator_name, _score);
            
        }
    
    function countPortfolioCerts() view public returns(uint){
        return Portfolio_CertList.length;
    }
    
    function isCertificateValid(string memory _cert_id) view public returns(bool){
        return Portfolio_Certs[_cert_id].isValid;
    }
    
    function getCertificateHash(string memory _cert_id) view public returns(string memory){
        return Portfolio_Certs[_cert_id].cert_Hash;
    }


    function getCertificateInfo(string memory _cert_id)
        view
        public
        returns(string memory, 
                string memory, 
                string memory, 
                string memory, 
                uint256,
                string memory, 
                bool)
        {
            return(
                Portfolio_Certs[_cert_id].pf_id,
                Portfolio_Certs[_cert_id].pf_name,
                Portfolio_Certs[_cert_id].reg_name,
                Portfolio_Certs[_cert_id].evaluator_name,
                Portfolio_Certs[_cert_id].score,
                Portfolio_Certs[_cert_id].evaluator_pk,
                Portfolio_Certs[_cert_id].isValid );
    }
    
}
    