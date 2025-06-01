const express = require('express');
const mysql = require('mysql');
const bcrypt = require('bcrypt');
const _ = require('lodash');

const app = express();
app.use(express.json());

// function maskPassword(password) {
//     if (typeof password !== 'string') return '';
//     return '*'.repeat(password.length);
// }

// app.post('/login', (req, res) => {
//     const { username, password } = req.body;
//     console.log('Received login attempt:', username, maskPassword(password));
//     const query = `SELECT * FROM users WHERE username = '${username}' AND password = '${password}'`;
//     // This is vulnerable to SQL injection
//     console.log('Executing query:', query);
//     res.json({ message: 'Login attempt logged' });
// });

// Vulnerability 2: Hardcoded secrets
const API_KEY = "sk-1234567890abcdef";
const DB_PASSWORD = "admin123";
console.log('API Key:', API_KEY);
console.log('Database password:', DB_PASSWORD); 
// Vulnerability 3: Insecure random number generation
app.get('/token', (req, res) => {
    const token = Math.random().toString(36);
    res.json({ token });
});

// Vulnerability 4: Prototype pollution via lodash
app.post('/merge', (req, res) => {
    const result = _.merge({}, req.body);
    console.log('Merged object:', result);
    res.json(result);
});

app.get('/getCreditCardDetails', (req, res) => {
    const cardId = req.query.id;
    //printing the card id
    console.log('Received card Id:', cardId);
    // Vulnerable: user input directly in SQL query
    const query = `SELECT * FROM users WHERE cardId = '${cardId}' '`;
    const creditCardNumber = query.creditCardNumber;
    console.log('Credit card number:', creditCardNumber);
});

app.listen(3000, () => {
    console.log('Server running on port 3000');
});

module.exports = app;