// SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.4.16 <0.8.7;
contract PortfolioManager{
    
    event newPortfolioCreated(string _pf_id, string _reg_name, string _reg_timestamp, string _evaluator_name, uint256 _score);
    
    struct Portfolio{
        string pf_id;
        string pf_name;
        string reg_timestamp;
        string reg_name;
        string evaluator_name;
        string evaluator_pk;
        uint256 score;
        string pf_status;
        string pf_url;
    }
    
    mapping(string => Portfolio) Portfolios;
    string[] public PortfolioList;
    
    function newPortfolio(
        string memory _pf_id,
        string memory _pf_name,
        string memory _reg_timestamp,
        string memory _reg_name,
        string memory _evaluator_name,
        string memory _evaluator_pk,
        uint256 _score,
        string memory _pf_status,
        string memory _pf_url) 
        public{
            Portfolios[_pf_id].pf_id = _pf_id;
            Portfolios[_pf_id].pf_name = _pf_name;
            Portfolios[_pf_id].reg_timestamp = _reg_timestamp;
            Portfolios[_pf_id].reg_name = _reg_name;
            Portfolios[_pf_id].evaluator_name = _evaluator_name;
            Portfolios[_pf_id].evaluator_pk = _evaluator_pk;
            Portfolios[_pf_id].score = _score;
            Portfolios[_pf_id].pf_status = _pf_status;
            Portfolios[_pf_id].pf_url = _pf_url;
        
        PortfolioList.push(_pf_id);
        
        emit newPortfolioCreated(_pf_id, _reg_name, _reg_timestamp, _evaluator_name, _score);

    }
    
    function countPortfolio() view public returns(uint){
        return PortfolioList.length;
    }
    
    function getPortfolioStatus(string memory _pf_id)
        view
        public
        returns(string memory)
        {
            return(
            Portfolios[_pf_id].pf_status );
        }
    
    function getPortfolioURL(string memory _pf_id)
        view
        public
        returns(string memory)
        {
            return(
            Portfolios[_pf_id].pf_url);
        }
    
    function getPortfolioInfo(string memory _pf_id)
        view
        public
        returns(string memory, string memory, string memory, string memory, string memory,  string memory, uint256)
        {
            return(Portfolios[_pf_id].pf_id,
            Portfolios[_pf_id].pf_name,
            Portfolios[_pf_id].reg_timestamp,
            Portfolios[_pf_id].reg_name,
            Portfolios[_pf_id].evaluator_name,
            Portfolios[_pf_id].evaluator_pk,
            Portfolios[_pf_id].score );
        }
}