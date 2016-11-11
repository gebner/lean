/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include <string>
#include <vector>
#include "library/messages.h"

namespace lean {

message::message(parser_exception const & ex) :
        message(ex.get_file_name(), pos_info(ex.get_line(), ex.get_pos()),
                ERROR, ex.get_msg()) {}

void message_buffer::start_bucket(message_bucket_id const &) {}
void message_buffer::report(message_bucket_id const &, message const &) {}
void message_buffer::finish_bucket(message_bucket_id const &, std::vector<name> const &) {}

void stream_message_buffer::report(message_bucket_id const &, message const & msg) {
    if (msg.get_severity() != INFORMATION) {
        m_out->get_stream() << msg.get_file_name()
                            << ":" << msg.get_pos().first << ":" << msg.get_pos().second << ": ";
        switch (msg.get_severity()) {
            case INFORMATION: break;
            case WARNING: m_out->get_stream() << "warning: "; break;
            case ERROR:   m_out->get_stream() << "error: ";   break;
        }
        if (!msg.get_caption().empty())
            m_out->get_stream() << msg.get_caption() << ":\n";
    }
    m_out->get_stream() << msg.get_text() << "\n";
}

LEAN_THREAD_PTR(message_buffer, g_msg_buf);
scoped_message_buffer::scoped_message_buffer(message_buffer * buf) :
    m_old(g_msg_buf) { g_msg_buf = buf; }
scoped_message_buffer::~scoped_message_buffer() { g_msg_buf = m_old; }

message_buffer & get_global_message_buffer() {
    if (g_msg_buf) {
        return *g_msg_buf;
    } else {
        throw exception("global message buffer not initialized");
    }
}

LEAN_THREAD_PTR(scope_message_context, g_msg_ctx);

message_bucket_id get_global_msg_bucket_id() {
    return get_scope_message_context().get_bucket_id();
}

void report_message(message const & msg) {
    get_global_message_buffer().report(get_global_msg_bucket_id(), msg);
}

scope_message_context & get_scope_message_context() {
    if (g_msg_ctx) {
        return *g_msg_ctx;
    } else {
        throw exception("message context not initialized");
    }
}

scope_message_context::scope_message_context(message_bucket_id const & bucket) :
        scope_message_context(bucket, {}) {}
scope_message_context::scope_message_context(message_bucket_id const & bucket,
                                             std::vector<name> const & sub_buckets_to_reuse) :
        m_old(g_msg_ctx), m_bucket(bucket), m_sub_buckets(sub_buckets_to_reuse) {
    g_msg_ctx = this;
    get_global_message_buffer().start_bucket(m_bucket);
    DEBUG_CODE(for (auto & b : m_sub_buckets) lean_assert(b.get_prefix() == m_bucket.m_bucket););
}
scope_message_context::scope_message_context() :
    scope_message_context(g_msg_ctx->new_sub_bucket()) {}
scope_message_context::scope_message_context(std::string const & sub_name) :
    scope_message_context(g_msg_ctx->new_sub_bucket(sub_name)) {}
scope_message_context::scope_message_context(std::string const & sub_name, std::vector<name> const & sub_buckets_to_reuse) :
    scope_message_context(g_msg_ctx->new_sub_bucket(sub_name), sub_buckets_to_reuse) {}
scope_message_context::~scope_message_context() {
    get_global_message_buffer().finish_bucket(m_bucket, m_sub_buckets);
    g_msg_ctx = m_old;
}
message_bucket_id scope_message_context::new_sub_bucket() {
    unsigned i = static_cast<unsigned>(m_sub_buckets.size());
    name n(m_bucket.m_bucket, i);
    // TODO(gabriel): check if exists
    m_sub_buckets.push_back(n);
    return { n, m_bucket.m_version };
}
message_bucket_id scope_message_context::new_sub_bucket(std::string const & s) {
    name n(m_bucket.m_bucket, s.c_str());
    // TODO(gabriel): check if exists
    m_sub_buckets.push_back(n);
    return { n, m_bucket.m_version };
}

}
