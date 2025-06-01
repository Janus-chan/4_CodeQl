// More hardcoded secrets
const config = {
    database: {
        host: 'localhost',
        user: 'root',
        password: 'password123',
        database: 'webapp'
    },
    jwt_secret: 'my-super-secret-key',
    api_keys: {
        stripe: 'sk_test_123456789',
        aws: 'AKIAIOSFODNN7EXAMPLE'
    }
};

module.exports = config;